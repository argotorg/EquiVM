import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.AdminTrace

variable {fork : Ethereum.Fork}

/-!
# Midnight `setFeeSetter(address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 3423; reach lemma `midnightReachSetFeeSetterBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

/-- `setFeeSetter(address)`: the theorem `Correct.lean` routes selector 37 to. -/
theorem midnightSetFeeSetterBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hfork : fork ≥ .osaka)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 37)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 37) rfl hsel
  have hd : dispatchMsg contract I.calldata = some setFeeSetterTransition := by
    apply midnightDispatch_setFeeSetter <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachSetFeeSetterBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_3423_fallthrough (by simp) hwv rd
    by_cases hhi : I.calldata.size < calldataLimit
    · by_cases h36 : 36 ≤ I.calldata.size
      · have rd2 := midnightBlocks.midnight_block_3429_fallthrough (by simp)
          (entrySizeCheck_ok (bytes := 32) h36 hhi hsize) rd1
        have rd3 := midnightBlocks.midnight_block_3441 (by simp) (by jump_dest) rd2
        simp only [midnightBlocks.midnight_block_3441_stack] at rd3
        by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨k4, C4, rd4⟩ := midnightAddress4_ok (by simp) (by jump_dest) hcanon rd3
          have hdec := midnightDecodeAddress "newFeeSetter" (by decide) (by decide)
            h36 hhi hsize hcanon
          by_cases hauth : solcSourceWord I = UInt256.land (solcSlotWordAt ⟨9⟩ σ I) solcAddrMask
          · obtain ⟨k5, C5, rd5⟩ := midnightBlocks.midnight_block_3448_fallthrough (by simp)
              (by rw [addressMask_computed]; exact u256_sub_eq_zero_iff_eq.mpr hauth) rd4
            by_cases hperm : I.perm = true
            · have hr := adminSetterTraceReturn ⟨0, by decide⟩ hperm rd5
              have hbody := adminAddressReturns (fork := fork) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                "feeSetter" "newFeeSetter" "SetFeeSetter" ⟨10⟩ (calldataWord I.calldata 4)
                hcanon (by decide) (by decide) (by decide) (by decide) rfl rfl hwv hhi hauth hperm
              exact hr.reEquivExecutionGen hcode hd hdec hbody
                (storageWordWrite_accounts (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) rfl ⟨10⟩
                  (fun old ↦ setAddressOffset0Word old (calldataWord I.calldata 4)))
                voidReturnEquiv
            · have hp : I.perm = false := by cases h : I.perm <;> simp_all
              have hr := adminSetterTraceStatic ⟨0, by decide⟩ (by simp) hp rd5
              exact hr.reEquivStaticHalt hcode hd hdec
                (adminAddressStatic (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                  "feeSetter" "newFeeSetter" "SetFeeSetter" ⟨10⟩ (calldataWord I.calldata 4)
                  hcanon (by decide) (by decide) (by decide) (by decide) rfl rfl hwv hhi hauth hp)
          · obtain ⟨k5, C5, rd5⟩ := midnightBlocks.midnight_block_3448_taken (by simp)
              (by rw [addressMask_computed]; exact fun h ↦ hauth (u256_sub_eq_zero_iff_eq.mp h))
              (by jump_dest) rd4
            have hr := midnightBlocks.midnight_block_1415 (by simp) rd5
            exact hr.reEquivExecutionRevert hcode hd hdec
              (adminAddressReverts (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                "feeSetter" "newFeeSetter" "SetFeeSetter" (calldataWord I.calldata 4)
                (by decide) hwv hhi hauth)
        · have hr := midnightAddress4_revert (by simp) hcanon rd3
          exact hr.reEquivDecodingFailed hcode hd
            (midnightDecodeAddress_none_noncanon "newFeeSetter" h36 hhi hsize hcanon)
      · have rd2 := midnightBlocks.midnight_block_3429_taken (by simp)
          (by
            have hc : UInt256.slt
                (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
                (UInt256.ofNat 32) = ⟨1⟩ :=
              entrySizeCheck_short hsz (Nat.lt_of_not_ge h36) (by decide) hsize
            rw [hc]; decide) (by jump_dest) rd1
        have hr := midnightBlocks.midnight_block_712 (by simp) rd2
        exact hr.reEquivDecodingFailed hcode hd
          (midnightDecodeScalar_none_short "newFeeSetter" .address hsz (Nat.lt_of_not_ge h36) hsize)
    · have rd2 := midnightBlocks.midnight_block_3429_taken (by simp)
        (by
          have hc : UInt256.slt
              (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
              (UInt256.ofNat 32) = ⟨1⟩ := entrySizeCheck_huge (Nat.le_of_not_lt hhi) hsize (by decide)
          rw [hc]; decide) (by jump_dest) rd1
      have hr := midnightBlocks.midnight_block_712 (by simp) rd2
      exact hr.reEquivDecodingFailed hcode hd
        (midnightDecodeScalar_none_huge "newFeeSetter" .address (Nat.le_of_not_lt hhi) hsize)
  · have rd1 := midnightBlocks.midnight_block_3423_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_712 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (setFeeSetterTransition.params.map Param.name)
        (transitionSignature setFeeSetterTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args =>
      exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)


end Benchmarks.Midnight
