import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.UpdatePositionEntry
import Benchmarks.Midnight.UpdatePositionSource
import Benchmarks.Midnight.TouchMarketCapacity
import Benchmarks.Midnight.ReturnThree128

/-!
# Midnight `updatePosition((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address),address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 15847; reach lemma `midnightReachUpdatePositionBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

/-- `updatePosition((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address),address)`: the theorem `Correct.lean` routes selector 12 to. -/
theorem midnightUpdatePositionBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwf : midnightWF σ I)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 12)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 12) rfl hsel
  have hd : dispatchMsg contract I.calldata = some updatePositionTransition := by
    apply midnightDispatch_updatePosition <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachUpdatePositionBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  change RD midnightBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
    ⟨15847⟩ [solcSelectorWord I] midnightEntryMemory (UInt256.ofNat 26) ByteArray.empty σ k C at rd
  have ha : MemoryAccounting midnightEntryMemory (UInt256.ofNat 26) C := by
    refine ⟨MemoryPaid.entry C, ?_⟩
    change midnightEntryMemory.size ≤ 832
    rw [midnightEntryMemory_size]
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_15847_fallthrough (by simp) hwv rd
    have ha1 := memoryAccountingAt rd1 (by memory_account ha)
    have hselector : ¬ 0xac9650d8 = (bytesToWord (I.calldata.toList.take 4)).toNat := by
      rw [calldataSelector_of_selIs hsel]
      decide +kernel
    rcases midnightUpdatePositionEntry (by simp) hsz hsize hselector
        midnightEntryMemory_freePtr ha1 rd1 with
      ⟨hdec, hr⟩ | ⟨m, hdec, h68, hhi, hu, mem', root, aw2, k2, C2,
        hroot, hm, hfree, hmem, ha2, rd2⟩
    · exact hr.reEquivDecodingFailed hcode hd hdec
    · let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let user := calldataWord I.calldata 36
      have hlimit : I.calldata.size < calldataLimit := by
        change I.calldata.size < 2^255 + 4
        omega
      rcases midnightTouchMarketInternal_bounded (evm := evm) (g := Sat256.ofUInt256 g)
          (imms := ∅) m (by simp) hm hmem hgas ha2 hfree rfl (by jump_dest) rd2 with
        hoog | ⟨hr, hs⟩ | ⟨hr, hs⟩ |
          ⟨frame', evm', σ', out, mem'', free, aw3, k3, C3, hs, htouch,
            hp, hfreeLo, hfreeHi, _, hfree', rd3⟩
      · exact reEquiv_outOfGas (Xi_error_of_X (by rw [← hcode] at hoog; exact hoog))
      · exact hr.reEquivExecutionRevert hcode hd hdec
          (updatePositionTouchReverts hwv hlimit hs)
      · exact hr.reEquivStaticHalt hcode hd hdec
          (updatePositionTouchStatic hwv hlimit hs)
      · have hm' := hm.preserve hp
        have hmemory : 1088 ≤ mem''.size := hm'.words.size
        have hmaturity : memLoad ((⟨832⟩ : UInt256) + UInt256.ofNat 128) mem'' =
            m.maturity := hm'.words.load_offset ⟨4, by change 4 < 8; decide⟩ rfl
        have hlo : 96 ≤ free.toNat := by omega
        have rd4 := midnightBlocks.midnight_block_15919 (by simp) (by jump_dest) rd3
        have hrun := midnightPositionUpdateInternal (evm := evm') (s0 := evm)
          (g := Sat256.ofUInt256 g) (imms := ∅) (m := m) (ptr := ⟨832⟩)
          (id := m.id) (user := user) (root := free) (ret := ⟨2594⟩)
          (R := [⟨1184⟩, solcSelectorWord I])
          (by simp) hu (by decide) (by change 992 ≤ mem''.size; omega)
          hmaturity hlo hfreeHi hfree' (by jump_dest)
          (by simpa only [hs.env, ← hs.accounts] using rd4)
        rcases hrun with ⟨hr, hbody⟩ | ⟨hr, hbody⟩ |
          ⟨hc, hpending, hf, hbody, aw4, k4, C4, rd5⟩
        · exact hr.reEquivExecutionRevert hcode hd hdec
            (updatePositionBodyReverts hwv hlimit htouch hbody)
        · exact hr.reEquivStaticHalt hcode hd hdec
            (updatePositionBodyStatic hwv hlimit htouch hbody)
        · have hfreeFinal := positionUpdateLogMemory_free mem'' free evm' m m.id user
            (by omega) hlo hfree'
          have hr := midnightReturnThree128 (by simp) hfreeHi hfreeFinal hc hpending hf rd5
          exact hr.reEquivExecutionGen hcode hd hdec
            (updatePositionBodyReturns hwv hlimit htouch hbody) rfl
            (returnEquiv.returned rfl (threeUint128ReturnEncoding _ _ _ hc hpending hf))
  · have rd1 := midnightBlocks.midnight_block_15847_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_6350 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (updatePositionTransition.params.map Param.name)
        (transitionSignature updatePositionTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args => exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Midnight
