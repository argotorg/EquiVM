import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.AddressDecode
import Benchmarks.Midnight.AdminSource

variable {fork : Ethereum.Fork}

/-!
# Midnight `setConfigurator(address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 4858; reach lemma `midnightReachSetConfiguratorBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem setConfiguratorTraceStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {value old : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024) (hperm : I.perm = false)
    (rd : RD fork midnightBytecode I g s0 ⟨4904⟩ (value :: old :: R) mem aw rdata σ k C) :
    RDstatic fork midnightBytecode g s0 := by
  -- The successful block requires write permission; follow its prefix to the forbidden SSTORE.
  have r1 := rd.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.sub (by native_decide) (by evm_ov)
  have r6 := r5.and (by native_decide) (by evm_ov)
  have r7 := r6.dup1 (by native_decide) (by evm_ov)
  have r8 := r7.swap2 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r12 := r11.shl (by native_decide) (by evm_ov)
  have r13 := r12.sub (by native_decide) (by evm_ov)
  have r14 := r13.not (by native_decide) (by evm_ov)
  have r15 := r14.and (by native_decide) (by evm_ov)
  have r16 := r15.or (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 9) (by native_decide) (by evm_ov)
  exact r17.sstoreStatic hperm (by native_decide) (by evm_ov)

theorem setConfiguratorTraceReturn {σ σ₀ A I} {g : Sat256} {k C : Nat} {aw value : UInt256}
    (hperm : I.perm = true)
    (rd : RD fork midnightBytecode I g (initState σ σ₀ g A I) ⟨4904⟩
      [value, solcSlotWordAt ⟨9⟩ σ I, solcSelectorWord I] midnightEntryMemory aw
      ByteArray.empty σ k C) :
    RDret fork midnightBytecode g (initState σ σ₀ g A I)
      (sstoreAccountMap I.codeOwner σ ⟨9⟩ (setAddressOffset0Word (solcSlotWordAt ⟨9⟩ σ I) value))
      ByteArray.empty := by
  have hr := midnightBlocks.midnight_block_4904 (by simp) hperm rd
  simp only [addressMask_computed, midnightEntryMemory_zero,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl, byteArray_readWithPadding_zero] at hr
  simpa only [setAddressOffset0Word, u256_land_comm] using hr

/-- `setConfigurator(address)`: the theorem `Correct.lean` routes selector 31 to. -/
theorem midnightSetConfiguratorBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hfork : fork ≥ .osaka)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 31)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 31) rfl hsel
  have hd : dispatchMsg contract I.calldata = some setConfiguratorTransition := by
    apply midnightDispatch_setConfigurator <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachSetConfiguratorBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_4858_fallthrough (by simp) hwv rd
    by_cases hhi : I.calldata.size < calldataLimit
    · by_cases h36 : 36 ≤ I.calldata.size
      · have rd2 := midnightBlocks.midnight_block_4864_fallthrough (by simp)
          (entrySizeCheck_ok (bytes := 32) h36 hhi hsize) rd1
        have rd3 := midnightBlocks.midnight_block_4876 (by simp) (by jump_dest) rd2
        simp only [midnightBlocks.midnight_block_4876_stack] at rd3
        by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨k4, C4, rd4⟩ := midnightAddress4_ok (by simp) (by jump_dest) hcanon rd3
          have hdec := midnightDecodeAddress "newConfigurator" (by decide) (by decide)
            h36 hhi hsize hcanon
          by_cases hauth : solcSourceWord I = UInt256.land (solcSlotWordAt ⟨9⟩ σ I) solcAddrMask
          · obtain ⟨k5, C5, rd5⟩ := midnightBlocks.midnight_block_4883_fallthrough (by simp)
              (by rw [addressMask_computed]; exact u256_sub_eq_zero_iff_eq.mpr hauth) rd4
            simp only [midnightBlocks.midnight_block_4883_fallthrough_stack] at rd5
            by_cases hperm : I.perm = true
            · have hr := setConfiguratorTraceReturn hperm rd5
              have hbody := adminAddressReturns (fork := fork) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                "configurator" "newConfigurator" "SetConfigurator" ⟨9⟩ (calldataWord I.calldata 4)
                hcanon (by decide) (by decide) (by decide) (by decide) rfl rfl hwv hhi hauth hperm
              exact hr.reEquivExecutionGen hcode hd hdec hbody
                (storageWordWrite_accounts (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) rfl ⟨9⟩
                  (fun old ↦ setAddressOffset0Word old (calldataWord I.calldata 4)))
                voidReturnEquiv
            · have hp : I.perm = false := by cases h : I.perm <;> simp_all
              have hr := setConfiguratorTraceStatic (by simp) hp rd5
              exact hr.reEquivStaticHalt hcode hd hdec
                (adminAddressStatic (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                  "configurator" "newConfigurator" "SetConfigurator" ⟨9⟩ (calldataWord I.calldata 4)
                  hcanon (by decide) (by decide) (by decide) (by decide) rfl rfl hwv hhi hauth hp)
          · obtain ⟨k5, C5, rd5⟩ := midnightBlocks.midnight_block_4883_taken (by simp)
              (by rw [addressMask_computed]; exact fun h ↦ hauth (u256_sub_eq_zero_iff_eq.mp h))
              (by jump_dest) rd4
            have hr := midnightBlocks.midnight_block_1415 (by simp
              [midnightBlocks.midnight_block_4883_taken_stack]) rd5
            exact hr.reEquivExecutionRevert hcode hd hdec
              (adminAddressReverts (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                "configurator" "newConfigurator" "SetConfigurator" (calldataWord I.calldata 4)
                (by decide) hwv hhi hauth)
        · have hr := midnightAddress4_revert (by simp) hcanon rd3
          exact hr.reEquivDecodingFailed hcode hd
            (midnightDecodeAddress_none_noncanon "newConfigurator" h36 hhi hsize hcanon)
      · have rd2 := midnightBlocks.midnight_block_4864_taken (by simp)
          (by
            have hc : UInt256.slt
                (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
                (UInt256.ofNat 32) = ⟨1⟩ :=
              entrySizeCheck_short hsz (Nat.lt_of_not_ge h36) (by decide) hsize
            rw [hc]; decide) (by jump_dest) rd1
        have hr := midnightBlocks.midnight_block_712 (by simp) rd2
        exact hr.reEquivDecodingFailed hcode hd
          (midnightDecodeScalar_none_short "newConfigurator" .address hsz (Nat.lt_of_not_ge h36) hsize)
    · have rd2 := midnightBlocks.midnight_block_4864_taken (by simp)
        (by
          have hc : UInt256.slt
              (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
              (UInt256.ofNat 32) = ⟨1⟩ := entrySizeCheck_huge (Nat.le_of_not_lt hhi) hsize (by decide)
          rw [hc]; decide) (by jump_dest) rd1
      have hr := midnightBlocks.midnight_block_712 (by simp) rd2
      exact hr.reEquivDecodingFailed hcode hd
        (midnightDecodeScalar_none_huge "newConfigurator" .address (Nat.le_of_not_lt hhi) hsize)
  · have rd1 := midnightBlocks.midnight_block_4858_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_712 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (setConfiguratorTransition.params.map Param.name)
        (transitionSignature setConfiguratorTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args =>
      exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Midnight
