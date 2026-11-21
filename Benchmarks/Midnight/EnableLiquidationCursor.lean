import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.EnableSource
import Benchmarks.Midnight.ScalarDecode
import Benchmarks.Midnight.AddressDecode
import Benchmarks.Midnight.WordArray

/-!
# Midnight `enableLiquidationCursor(uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 9288; reach lemma `midnightReachEnableLiquidationCursorBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem enableLiquidationCursorTraceStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024) (hperm : I.perm = false)
    (rd : RD midnightBytecode I g s0 ⟨9343⟩ (x0 :: R) mem aw rdata σ k C) :
    RDstatic midnightBytecode g s0 := by
  let r0 := rd
  have r1 := r0.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 79500581542694580879866357852714598442727624000408534142154866172540330550542) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r4 := r3.swap3 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 8) (by native_decide) (by evm_ov)
  have r9 := r8.dup3 (by native_decide) (by evm_ov)
  have r10 := RD.genMstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r13 := RD.genMload r12 (by native_decide) (by evm_ov)
  have r14 := RD.genKeccak256 r13 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r17 := r16.not (by native_decide) (by evm_ov)
  have r18 := r17.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r19⟩ := RD.sload r18 (by native_decide) (by evm_ov)
  have r20 := r19.and (by native_decide) (by evm_ov)
  have r21 := r20.or (by native_decide) (by evm_ov)
  have r22 := r21.swap1 (by native_decide) (by evm_ov)
  exact r22.sstoreStatic hperm (by native_decide) (by evm_ov)

theorem enableLiquidationCursorTraceReturn {σ σ₀ A I} {g : Sat256} {k C : Nat} {aw value : UInt256}
    (hperm : I.perm = true)
    (rd : RD midnightBytecode I g (initState σ σ₀ g A I) ⟨9343⟩
      [value, solcSelectorWord I] midnightEntryMemory aw ByteArray.empty σ k C) :
    RDret midnightBytecode g (initState σ σ₀ g A I)
      (sstoreAccountMap I.codeOwner σ (solcMappingSlot ⟨8⟩ value)
        (UInt256.lor (UInt256.land (solcSlotWordAt (solcMappingSlot ⟨8⟩ value) σ I)
          (UInt256.lnot ⟨255⟩)) ⟨1⟩)) ByteArray.empty := by
  have hr := midnightBlocks.midnight_block_9343 (by simp) hperm rd
  simp only [midnightEntryMemory_zero,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl,
    wordAt0_fold, twoWordHash_fold, mappingMemory_fold, mappingMemory_zero,
    mappingMemory_hash, mappingMemory_freePtr] at hr
  have hz : memLoad (UInt256.ofNat 800)
      (writeWord (mappingMemory value ⟨8⟩) 832 value) = ⟨0⟩ := by
    rw [memLoad_writeWord_preserved _ _ _ _ (by rw [mappingMemory_size]; decide)
      (Or.inl (by decide)), mappingMemory_zero]
  change RDret _ _ _ _ ((writeWord (mappingMemory value ⟨8⟩) 832 value).readWithPadding
    (memLoad (UInt256.ofNat 800) (writeWord (mappingMemory value ⟨8⟩) 832 value)).toNat
    (memLoad (UInt256.ofNat 800) (writeWord (mappingMemory value ⟨8⟩) 832 value)).toNat) at hr
  simpa only [hz, show (⟨0⟩ : UInt256).toNat = 0 from rfl, byteArray_readWithPadding_zero] using hr

/-- `enableLiquidationCursor(uint256)`: the theorem `Correct.lean` routes selector 25 to. -/
theorem midnightEnableLiquidationCursorBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwf : midnightWF σ I)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 25)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 25) rfl hsel
  have hd : dispatchMsg contract I.calldata = some enableLiquidationCursorTransition := by
    apply midnightDispatch_enableLiquidationCursor <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachEnableLiquidationCursorBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_9288_fallthrough (by simp) hwv rd
    by_cases hhi : I.calldata.size < calldataLimit
    · by_cases h36 : 36 ≤ I.calldata.size
      · have rd2 := midnightBlocks.midnight_block_9294_fallthrough (by simp)
          (entrySizeCheck_ok (bytes := 32) h36 hhi hsize) rd1
        have hdec := midnightDecodeUint256 "liquidationCursor" (by decide) (by decide) h36 hhi hsize
        by_cases hauth : solcSourceWord I = UInt256.land (solcSlotWordAt ⟨9⟩ σ I) solcAddrMask
        · obtain ⟨k3, C3, rd3⟩ := midnightBlocks.midnight_block_9306_fallthrough (by simp)
            (by rw [addressMask_computed]; exact u256_sub_eq_zero_iff_eq.mpr hauth) rd2
          simp only [midnightBlocks.midnight_block_9306_fallthrough_stack] at rd3
          change RD _ _ _ _ _ [calldataWord I.calldata 4, solcSelectorWord I] _ _ _ _ _ _ at rd3
          by_cases hbound : (calldataWord I.calldata 4).toNat < 1000000000000000000
          · have rd4 := midnightBlocks.midnight_block_9327_fallthrough (by simp)
              (by rw [ult_one (a := calldataWord I.calldata 4) (b := UInt256.ofNat 1000000000000000000) hbound]; decide) rd3
            by_cases hperm : I.perm = true
            · have hr := enableLiquidationCursorTraceReturn hperm rd4
              exact hr.reEquivExecutionGen hcode hd hdec
                (enableReturns (initState σ σ₀ (Sat256.ofUInt256 g) A I) true
                  (calldataWord I.calldata 4) hwv hhi hauth hbound hperm)
                (storageWordWrite_accounts (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) rfl
                  (solcMappingSlot ⟨8⟩ (calldataWord I.calldata 4))
                  (fun old ↦ UInt256.lor (UInt256.land old (UInt256.lnot ⟨255⟩)) ⟨1⟩))
                voidReturnEquiv
            · have hp : I.perm = false := by cases h : I.perm <;> simp_all
              have hr := enableLiquidationCursorTraceStatic (by simp) hp rd4
              exact hr.reEquivStaticHalt hcode hd hdec
                (enableStatic (initState σ σ₀ (Sat256.ofUInt256 g) A I) true
                  (calldataWord I.calldata 4) hwv hhi hauth hbound hp)
          · have rd4 := midnightBlocks.midnight_block_9327_taken (by simp)
              (by rw [ult_zero (a := calldataWord I.calldata 4) (b := UInt256.ofNat 1000000000000000000) (Nat.le_of_not_lt hbound)]; decide) (by jump_dest) rd3
            have hr := midnightBlocks.midnight_block_9420 (by simp) rd4
            exact hr.reEquivExecutionRevert hcode hd hdec
              (enableBoundReverts (initState σ σ₀ (Sat256.ofUInt256 g) A I) true
                (calldataWord I.calldata 4) hwv hhi hauth hbound)
        · obtain ⟨k3, C3, rd3⟩ := midnightBlocks.midnight_block_9306_taken (by simp)
            (by rw [addressMask_computed]; exact fun h ↦ hauth (u256_sub_eq_zero_iff_eq.mp h))
            (by jump_dest) rd2
          have hr := midnightBlocks.midnight_block_1415
            (by simp [midnightBlocks.midnight_block_9306_taken_stack]) rd3
          exact hr.reEquivExecutionRevert hcode hd hdec
            (enableAuthReverts (initState σ σ₀ (Sat256.ofUInt256 g) A I) true
              (calldataWord I.calldata 4) hwv hhi hauth)
      · have rd2 := midnightBlocks.midnight_block_9294_taken (by simp)
          (by
            have hc : UInt256.slt
                (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
                (UInt256.ofNat 32) = ⟨1⟩ :=
              entrySizeCheck_short hsz (Nat.lt_of_not_ge h36) (by decide) hsize
            rw [hc]; decide) (by jump_dest) rd1
        have hr := midnightBlocks.midnight_block_712 (by simp) rd2
        exact hr.reEquivDecodingFailed hcode hd
          (midnightDecodeScalar_none_short "liquidationCursor" (.int (.uint ⟨256, by decide⟩))
            hsz (Nat.lt_of_not_ge h36) hsize)
    · have rd2 := midnightBlocks.midnight_block_9294_taken (by simp)
        (by
          have hc : UInt256.slt
              (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
              (UInt256.ofNat 32) = ⟨1⟩ := entrySizeCheck_huge (Nat.le_of_not_lt hhi) hsize (by decide)
          rw [hc]; decide) (by jump_dest) rd1
      have hr := midnightBlocks.midnight_block_712 (by simp) rd2
      exact hr.reEquivDecodingFailed hcode hd
        (midnightDecodeScalar_none_huge "liquidationCursor" (.int (.uint ⟨256, by decide⟩))
          (Nat.le_of_not_lt hhi) hsize)
  · have rd1 := midnightBlocks.midnight_block_9288_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_712 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (enableLiquidationCursorTransition.params.map Param.name)
        (transitionSignature enableLiquidationCursorTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args => exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Midnight
