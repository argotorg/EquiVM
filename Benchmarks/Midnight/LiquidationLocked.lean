import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.AddressDecode
import Benchmarks.Midnight.PairDecode
import Benchmarks.Midnight.LockMemory
import Benchmarks.Midnight.Allocation

variable {fork : Ethereum.Fork}

/-!
# Midnight `liquidationLocked(bytes32,address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 18194; reach lemma `midnightReachLiquidationLockedBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem liquidationLockedTraceReturn {σ σ₀ A I} {g : Sat256} {k C : Nat} {user : UInt256}
    (hcanon : user.toNat < EVM.addressModulus)
    (rd : RD fork midnightBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 18224)
      [user, UInt256.ofNat 15471, UInt256.ofNat 32, solcSelectorWord I] midnightEntryMemory
      (M (M (UInt256.ofNat 0) (UInt256.ofNat 64) ⟨32⟩) (UInt256.ofNat 800) ⟨32⟩)
      ByteArray.empty σ k C) :
    RDret fork midnightBytecode g (initState σ σ₀ g A I) σ
      (UInt256.isZero (UInt256.isZero (codeOwnerTransientWord I σ
        (lockSlot liquidationLockBase (calldataWord I.calldata 4) user)))).toByteArray := by
  have rd1 := midnightBlocks.midnight_block_18224 (by simp) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_18224_stack] at rd1
  obtain ⟨aw2, k2, C2, rd2⟩ := midnightBlocks.midnight_block_23150_packed
    (by simp) (by jump_dest) rd1
  have hfp : memLoad (UInt256.ofNat 64) midnightEntryMemory = ⟨832⟩ := midnightEntryMemory_freePtr
  simp only [midnightBlocks.midnight_block_23150_stack,
    midnightBlocks.midnight_block_23150_memory, hfp, addressMask_computed,
    solcAddrMask_clean hcanon] at rd2
  change RD fork _ _ _ _ (UInt256.ofNat 18444)
    [UInt256.ofNat 832, UInt256.ofNat 128, UInt256.ofNat 23229,
     UInt256.ofNat 832, UInt256.ofNat 864, UInt256.ofNat 15471, UInt256.ofNat 32, solcSelectorWord I]
    (lockHashMemory (calldataWord I.calldata 4) user) aw2 ByteArray.empty σ k2 C2 at rd2
  obtain ⟨aw3, k3, C3, rd3⟩ := midnightAllocate (by simp) (by native_decide) (by jump_dest) rd2
  change RD fork _ _ _ _ (UInt256.ofNat 23229)
    [UInt256.ofNat 832, UInt256.ofNat 864, UInt256.ofNat 15471, UInt256.ofNat 32, solcSelectorWord I]
    (lockReturnMemory (calldataWord I.calldata 4) user) aw3 ByteArray.empty σ k3 C3 at rd3
  obtain ⟨aw4, k4, C4, rd4⟩ := midnightBlocks.midnight_block_23229_packed
    (by simp) (by jump_dest) rd3
  have hh : keccakWord (UInt256.ofNat 864) ⟨96⟩
      (lockReturnMemory (calldataWord I.calldata 4) user) =
      lockSlot liquidationLockBase (calldataWord I.calldata 4) user := lockReturnMemory_hash _ _
  simp only [midnightBlocks.midnight_block_23229_stack,
    lockReturnMemory_length, hh] at rd4
  have hr := midnightBlocks.midnight_block_15471 (by simp) rd4
  rw [lockReturnMemory_freePtr] at hr
  exact (writeWord_sparse_read_back _ _ _) ▸ hr

/-- `liquidationLocked(bytes32,address)`: the theorem `Correct.lean` routes selector 0 to. -/
theorem midnightLiquidationLockedBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hfork : fork ≥ .osaka)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 0)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 0) rfl hsel
  have hd : dispatchMsg contract I.calldata = some liquidationLockedTransition := by
    apply midnightDispatch_liquidationLocked
    exact hsel
  obtain ⟨k, C, rd⟩ := midnightReachLiquidationLockedBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_18194_fallthrough (by simp) hwv rd
    by_cases hhi : I.calldata.size < calldataLimit
    · by_cases h68 : 68 ≤ I.calldata.size
      · have rd2 := midnightBlocks.midnight_block_18200_fallthrough (by simp)
          (entrySizeCheck_ok (bytes := 64) h68 hhi hsize) rd1
        have rd3 := midnightBlocks.midnight_block_18212 (by simp) (by jump_dest) rd2
        simp only [midnightBlocks.midnight_block_18212_stack] at rd3
        by_cases hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus
        · obtain ⟨k4, C4, rd4⟩ := midnightAddress36_ok (by simp) (by jump_dest) hcanon rd3
          have hret := liquidationLockedTraceReturn hcanon rd4
          have hdec := midnightDecodeBytes32Address "id" "user"
            (by decide) (by decide) (by decide) (by decide) h68 hhi hsize hcanon
          have hbody := liquidationLockedBodyReturns (fork := fork)
            (initState σ σ₀ (Sat256.ofUInt256 g) A I)
            (calldataWord I.calldata 4) (calldataWord I.calldata 36) hcanon hwv hhi
          exact hret.reEquivExecution hcode hd hdec hbody
            (by
              unfold lockValue
              change returnEquiv _ (some [wordToElem .bool (Stele.EVM.transientLoad
                (initState σ σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner
                (lockSlot liquidationLockBase (calldataWord I.calldata 4)
                  (calldataWord I.calldata 36)))]) _
              rw [codeOwnerTransientWord_initState]
              exact returnEquiv_of_encode (fullBoolWordReturnEncoding _))
        · have hr := midnightAddress36_revert (by simp) hcanon rd3
          exact hr.reEquivDecodingFailed hcode hd
            (midnightDecodeBytes32Address_none_noncanon "id" "user" h68 hhi hsize hcanon)
      · have rd2 := midnightBlocks.midnight_block_18200_taken (by simp)
          (by
            have hc : UInt256.slt
                (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
                (UInt256.ofNat 64) = ⟨1⟩ :=
              entrySizeCheck_short hsz (Nat.lt_of_not_ge h68) (by decide) hsize
            rw [hc]
            decide) (by jump_dest) rd1
        have hr := midnightBlocks.midnight_block_6350 (by simp) rd2
        exact hr.reEquivDecodingFailed hcode hd
          (midnightDecodePair_none_short "id" "user" (.bytes abiBytes32Width) .address
            hsz (Nat.lt_of_not_ge h68) hsize)
    · have rd2 := midnightBlocks.midnight_block_18200_taken (by simp)
        (by
          have hc : UInt256.slt
              (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
              (UInt256.ofNat 64) = ⟨1⟩ :=
            entrySizeCheck_huge (Nat.le_of_not_lt hhi) hsize (by decide)
          rw [hc]
          decide) (by jump_dest) rd1
      have hr := midnightBlocks.midnight_block_6350 (by simp) rd2
      exact hr.reEquivDecodingFailed hcode hd
        (midnightDecodePair_none_huge "id" "user" (.bytes abiBytes32Width) .address
          (Nat.le_of_not_lt hhi) hsize)
  · have rd1 := midnightBlocks.midnight_block_18194_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_6350 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (liquidationLockedTransition.params.map Param.name)
        (transitionSignature liquidationLockedTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args =>
      exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)




end Benchmarks.Midnight
