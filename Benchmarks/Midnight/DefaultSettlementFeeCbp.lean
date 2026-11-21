import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.AddressDecode
import Benchmarks.Midnight.PairDecode
import Benchmarks.Midnight.MappingMemory
import Benchmarks.Midnight.ArrayStorage
import Benchmarks.Midnight.PackedArray

/-!
# Midnight `defaultSettlementFeeCbp(address,uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 2923; reach lemma `midnightReachDefaultSettlementFeeCbpBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def defaultSettlementFeeArguments (loanToken : UInt256) (index : Nat) : Store :=
  nestedMappingArguments (.address (AccountAddress.ofNat loanToken.toNat)) (.int (Int.ofNat index))

def defaultSettlementFeeLoc (loanToken : UInt256) (index : Fin 7) : StorageLoc := {
  slot := solcMappingSlot ⟨4⟩ loanToken
  offset := ⟨2 * index.val, by omega⟩
  size := 2
  hbound := by change 2 * index.val + 2 - 1 < 32; have := index.isLt; omega
  type := .int (.uint ⟨16, by decide⟩) }

theorem defaultSettlementFeeBodyReturns (evm : EVM.State) (loanToken : UInt256) (index : Fin 7)
    (hcanon : loanToken.toNat < EVM.addressModulus)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) :
    ExecTransitionBody config contract evm (defaultSettlementFeeArguments loanToken index.val)
      defaultSettlementFeeCbpTransition.body
      (.returned (calldataFrame contract (defaultSettlementFeeArguments loanToken index.val) ∅ evm)
        evm (some [.int (Int.ofNat (UInt256.land (UInt256.shiftRight
          (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨4⟩ loanToken))
          (UInt256.ofNat (16 * index.val))) ⟨65535⟩).toNat)])) := by
  apply guardedMappingArrayGetter (t := .int (.uint ⟨16, by decide⟩))
    (loc := defaultSettlementFeeLoc loanToken index) (length := 7) evm _
    (.address (AccountAddress.ofNat loanToken.toNat)) index.val
    rfl rfl rfl rfl ?_ ?_ (by decide) (by decide) (by decide) index.isLt hwv hhi
  · have hi16 : index.val < 16 := by omega
    have hiword : index.val < UInt256.size := Nat.lt_trans index.isLt (by decide)
    simp only [keyValueToWord_address_of_canonical loanToken hcanon,
      keyValueToWord_int_ofNat_of_lt hiword, UInt256.toNat_ofNat_of_lt hiword,
      Nat.div_eq_of_lt hi16, Nat.mod_eq_of_lt hi16]
    change some (StorageAddr.leaf {
      slot := solcMappingSlot ⟨4⟩ loanToken + ⟨0⟩
      offset := Fin.ofNat 32 (index.val * 2)
      size := 2
      hbound := _
      type := .int (.uint ⟨16, by decide⟩) }) = _
    rw [u256_add_zero]
    congr 3
    apply Fin.ext
    change (index.val * 2) % 32 = 2 * index.val
    rw [Nat.mod_eq_of_lt (by omega), Nat.mul_comm]
  · unfold defaultSettlementFeeLoc
    rw [storageLocLoad_uint_offset evm _ ⟨2 * index.val, by omega⟩ 2 ⟨16, by decide⟩
      (by decide) (by have := index.isLt; omega) (by decide), div_byteOffset_eq_shiftRight]
    congr 6
    change 8 * (2 * index.val) = 16 * index.val
    omega

theorem defaultSettlementFeeBodyReverts (evm : EVM.State) (loanToken : UInt256) (index : Nat)
    (hi : ¬ index < 7) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) :
    ExecTransitionBody config contract evm (defaultSettlementFeeArguments loanToken index)
      defaultSettlementFeeCbpTransition.body .reverted := by
  exact guardedMappingArrayRevert evm _ (.address (AccountAddress.ofNat loanToken.toNat)) index
    rfl rfl (by decide) (by decide) (by decide) hi hwv hhi

theorem defaultSettlementFeeTraceReturn {σ σ₀ A I} {g : Sat256} {k C : Nat} {key : UInt256}
    (hcanon : key.toNat < EVM.addressModulus)
    (hi : (calldataWord I.calldata 36).toNat < 7)
    (rd : RD midnightBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 2948)
      [key, solcSelectorWord I] midnightEntryMemory
      (M (M (UInt256.ofNat 0) (UInt256.ofNat 64) ⟨32⟩) (UInt256.ofNat 800) ⟨32⟩)
      ByteArray.empty σ k C) :
    RDret midnightBytecode g (initState σ σ₀ g A I) σ
      (UInt256.land (UInt256.shiftRight (solcSlotWordAt (solcMappingSlot ⟨4⟩ key) σ I)
        (UInt256.ofNat (16 * (calldataWord I.calldata 36).toNat))) ⟨65535⟩).toByteArray := by
  have hc : UInt256.isZero (UInt256.lt (calldataWord I.calldata 36) (UInt256.ofNat 7)) = ⟨0⟩ := by
    rw [ult_one hi]; rfl
  obtain ⟨aw1, k1, C1, rd1⟩ := midnightBlocks.midnight_block_2948_fallthrough_packed
    (by simp) hc rd
  simp only [midnightBlocks.midnight_block_2948_fallthrough_stack,
    midnightBlocks.midnight_block_2948_fallthrough_memory, addressMask_computed,
    solcAddrMask_clean hcanon, midnightEntryMemory_zero] at rd1
  simp only [show (UInt256.ofNat 32).toNat = 32 from rfl,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl, wordAt0_fold, twoWordHash_fold,
    mappingMemory_fold, mappingMemory_zero, mappingMemory_hash] at rd1
  have rd2 := midnightBlocks.midnight_block_2989 (by simp) (by jump_dest) rd1
  simp only [midnightBlocks.midnight_block_2989_stack] at rd2
  obtain ⟨k3, C3, rd3⟩ := midnightUint16ArrayLocation (by simp) hi (by jump_dest) rd2
  have hr := midnightBlocks.midnight_block_2101 (by simp) rd3
  simp only [(uint16ArrayIndexFacts _ hi).2.2, mappingMemory_freePtr] at hr
  exact (mappingMemory_return _ _ _) ▸ hr

theorem defaultSettlementFeeTraceRevert {σ σ₀ A I} {g : Sat256} {k C : Nat} {key : UInt256}
    (hi : ¬ (calldataWord I.calldata 36).toNat < 7)
    (rd : RD midnightBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 2948)
      [key, solcSelectorWord I] midnightEntryMemory
      (M (M (UInt256.ofNat 0) (UInt256.ofNat 64) ⟨32⟩) (UInt256.ofNat 800) ⟨32⟩)
      ByteArray.empty σ k C) :
    RDrev midnightBytecode g (initState σ σ₀ g A I) := by
  have hc : UInt256.isZero (UInt256.lt (calldataWord I.calldata 36) (UInt256.ofNat 7)) ≠ ⟨0⟩ := by
    rw [ult_zero (show (UInt256.ofNat 7).toNat ≤ (calldataWord I.calldata 36).toNat from
      Nat.le_of_not_lt hi)]
    decide
  obtain ⟨aw1, k1, C1, rd1⟩ := midnightBlocks.midnight_block_2948_taken_packed
    (by simp) hc (by jump_dest) rd
  exact midnightBlocks.midnight_block_712 (by simp [midnightBlocks.midnight_block_2948_taken_stack]) rd1

/-- `defaultSettlementFeeCbp(address,uint256)`: the theorem `Correct.lean` routes selector 42 to. -/
theorem midnightDefaultSettlementFeeCbpBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwf : midnightWF σ I)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 42)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 42) rfl hsel
  have hd : dispatchMsg contract I.calldata = some defaultSettlementFeeCbpTransition := by
    apply midnightDispatch_defaultSettlementFeeCbp <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachDefaultSettlementFeeCbpBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_2923_fallthrough (by simp) hwv rd
    by_cases hhi : I.calldata.size < calldataLimit
    · by_cases h68 : 68 ≤ I.calldata.size
      · have rd2 := midnightBlocks.midnight_block_2929_fallthrough (by simp)
          (entrySizeCheck_ok (bytes := 64) h68 hhi hsize) rd1
        have rd3 := midnightBlocks.midnight_block_2941 (by simp) (by jump_dest) rd2
        simp only [midnightBlocks.midnight_block_2941_stack] at rd3
        by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨k4, C4, rd4⟩ := midnightAddress4_ok (by simp) (by jump_dest) hcanon rd3
          have hdec := midnightDecodePair_ok "arg0" "arg1"
            (by decide) (by decide) (by decide) (by decide) h68 hhi hsize
            (decodeAddressWord (by omega) hcanon) (decodeUint256Word h68)
          by_cases hi : (calldataWord I.calldata 36).toNat < 7
          · have hret := defaultSettlementFeeTraceReturn hcanon hi rd4
            have hbody := defaultSettlementFeeBodyReturns
              (initState σ σ₀ (Sat256.ofUInt256 g) A I)
              (calldataWord I.calldata 4) ⟨(calldataWord I.calldata 36).toNat, hi⟩ hcanon hwv hhi
            exact hret.reEquivExecution hcode hd hdec hbody
              (returnEquiv_of_encode (uintReturnEncoding ⟨16, by decide⟩ _
                (u256LandMaskToNatLtOfToNat _ _ (by decide))))
          · have hr := defaultSettlementFeeTraceRevert hi rd4
            exact hr.reEquivExecutionRevert hcode hd hdec
              (defaultSettlementFeeBodyReverts _ _ _ hi hwv hhi)
        · have hr := midnightAddress4_revert (by simp) hcanon rd3
          exact hr.reEquivDecodingFailed hcode hd
            (midnightDecodePair_none_left "arg0" "arg1" .address (.int (.uint ⟨256, by decide⟩))
              h68 hhi hsize (decodeAddressWord_none (by omega) hcanon))
      · have rd2 := midnightBlocks.midnight_block_2929_taken (by simp)
          (by
            have hc : UInt256.slt
                (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
                (UInt256.ofNat 64) = ⟨1⟩ :=
              entrySizeCheck_short hsz (Nat.lt_of_not_ge h68) (by decide) hsize
            rw [hc]
            decide) (by jump_dest) rd1
        have hr := midnightBlocks.midnight_block_712 (by simp) rd2
        exact hr.reEquivDecodingFailed hcode hd
          (midnightDecodePair_none_short "arg0" "arg1" .address (.int (.uint ⟨256, by decide⟩))
            hsz (Nat.lt_of_not_ge h68) hsize)
    · have rd2 := midnightBlocks.midnight_block_2929_taken (by simp)
        (by
          have hc : UInt256.slt
              (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
              (UInt256.ofNat 64) = ⟨1⟩ :=
            entrySizeCheck_huge (Nat.le_of_not_lt hhi) hsize (by decide)
          rw [hc]
          decide) (by jump_dest) rd1
      have hr := midnightBlocks.midnight_block_712 (by simp) rd2
      exact hr.reEquivDecodingFailed hcode hd
        (midnightDecodePair_none_huge "arg0" "arg1" .address (.int (.uint ⟨256, by decide⟩))
          (Nat.le_of_not_lt hhi) hsize)
  · have rd1 := midnightBlocks.midnight_block_2923_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_712 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (defaultSettlementFeeCbpTransition.params.map Param.name)
        (transitionSignature defaultSettlementFeeCbpTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args =>
      exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Midnight
