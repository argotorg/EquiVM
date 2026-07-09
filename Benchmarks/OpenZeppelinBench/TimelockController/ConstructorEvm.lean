import Benchmarks.OpenZeppelinBench.TimelockController.ConstructorDefs

/-!
# OpenZeppelin TimelockController constructor — EVM creation-bytecode trace

`tlcCtorInitcodeSuccess` : the payable creation bytecode halts returning the runtime, having applied
the five conditional `_grantRole` writes and `_minDelay = 86400` — i.e. the account map becomes
`tlcCtorFinalMap I σ`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace OpenZeppelinBench.TimelockController

/-! ## Section 0 — generic scratch-memory read lemmas

The two subroutines (`_singleton @360`, `_grantRole @450`) write to the solc scratch region
`mem[0 .. 0x40]` before hashing; `twoWordHashMem key slot M` is exactly those two `MSTORE`s
(`key` at `mem[0]`, `slot` at `mem[0x20]`) over a base memory `M`.  Unlike the runtime proofs, the
constructor's `M` is not exactly 96 bytes (the singletons grow it), so we re-derive the read-backs
for an arbitrary base of size `≥ 64`. -/

theorem tlcCtorEvmWordAt0_size {M : ByteArray} (key : UInt256) (hM : 32 ≤ M.size) :
    (wordAt0Mem key M).size = M.size := by
  unfold wordAt0Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
  omega

theorem tlcCtorEvmScratch_size {M : ByteArray} (key slot : UInt256) (hM : 64 ≤ M.size) :
    (twoWordHashMem key slot M).size = M.size := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [tlcCtorEvmWordAt0_size key (by omega)]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, tlcCtorEvmWordAt0_size key (by omega),
    toByteArray_size]
  omega

/-- The `KECCAK256(0, 0x40)` preimage after the two scratch stores is `key ‖ slot`. -/
theorem tlcCtorEvmScratch_read64 {M : ByteArray} (key slot : UInt256) (hM : 64 ≤ M.size) :
    (twoWordHashMem key slot M).readWithPadding 0 64 = key.toByteArray ++ slot.toByteArray := by
  have hw0 : 32 ≤ (wordAt0Mem key M).size := by rw [tlcCtorEvmWordAt0_size key (by omega)]; omega
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [tlcCtorEvmScratch_size key slot hM]; omega)]
  have hleft : (twoWordHashMem key slot M).extract 0 32 = key.toByteArray := by
    rw [← readWithPadding_eq_extract _ 0 (by rw [tlcCtorEvmScratch_size key slot hM]; omega)]
    unfold twoWordHashMem wordAt32Mem
    rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size]) hw0 (by omega)]
    unfold wordAt0Mem
    rw [write32_read_back _ _ 0 (by rw [toByteArray_size]) (by omega), toByteArray_extract_all]
  have hright : (twoWordHashMem key slot M).extract 32 64 = slot.toByteArray := by
    rw [← readWithPadding_eq_extract _ 32 (by rw [tlcCtorEvmScratch_size key slot hM]; omega)]
    unfold twoWordHashMem wordAt32Mem
    rw [write32_read_back _ _ 32 (by rw [toByteArray_size]) hw0, toByteArray_extract_all]
  rw [show (twoWordHashMem key slot M).extract 0 64 =
      (twoWordHashMem key slot M).extract 0 32 ++ (twoWordHashMem key slot M).extract 32 64 by
    rw [ByteArray.extract_append_extract]; norm_num, hleft, hright]

/-- The `KECCAK256` slot value produced by the scratch stores is `solcMappingSlot slot key`. -/
theorem tlcCtorEvmScratch_keccak {M : ByteArray} (key slot : UInt256) (hM : 64 ≤ M.size) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key slot M).readWithPadding 0 64))) =
      solcMappingSlot slot key := by
  rw [tlcCtorEvmScratch_read64 key slot hM]
  unfold solcMappingSlot
  exact mappingSlot_single key slot

/-- Scratch stores at `mem[0..0x40]` do not disturb a 32-byte read at any offset `≥ 64`. -/
theorem tlcCtorEvmScratch_read_above {M : ByteArray} (key slot : UInt256) (r : ℕ)
    (hr : 64 ≤ r) (hin : r + 32 ≤ M.size) :
    (twoWordHashMem key slot M).readWithPadding r 32 = M.readWithPadding r 32 := by
  have hw0 : 32 ≤ (wordAt0Mem key M).size := by rw [tlcCtorEvmWordAt0_size key (by omega)]; omega
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 r (by rw [toByteArray_size]) hw0 (by omega)
      (by rw [tlcCtorEvmWordAt0_size key (by omega)]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 r (by rw [toByteArray_size]) (by omega) (by omega) hin]

/-! ## Section 0b — memory-cost / active-word helpers

Every scratch/free-ptr memory access in `_grantRole` lands inside already-active memory (or has size
`0`), so its `memoryExpansionCost` is `0` and it leaves `activeWords` unchanged.  These let the grant
combinator run over a *symbolic* `aw` (only a lower bound is needed). -/

theorem tlcCtorEvmM_within (aw : UInt256) (off len : ℕ) (h : off + len ≤ 32 * aw.toNat) :
    MachineState.M aw.toNat off len = aw.toNat := by
  unfold MachineState.M; split
  · rfl
  · rw [Nat.max_eq_left]; omega

theorem tlcCtorEvmAwOut (aw : UInt256) (off len : ℕ) (h : off + len ≤ 32 * aw.toNat) :
    UInt256.ofNat (MachineState.M aw.toNat off len) = aw := by
  rw [tlcCtorEvmM_within aw off len h]; exact u256_ofNat_toNat aw

theorem tlcCtorEvmM_len0 (aw : UInt256) (off : ℕ) :
    MachineState.M aw.toNat off 0 = aw.toNat := rfl

theorem tlcCtorEvmAwOut0 (aw : UInt256) (off : ℕ) :
    UInt256.ofNat (MachineState.M aw.toNat off 0) = aw := by
  rw [tlcCtorEvmM_len0]; exact u256_ofNat_toNat aw

/-- Empty-source `CALLDATACOPY` (empty calldata) writing at or past the end of memory is a no-op. -/
theorem tlcCtorEvmEmptyWrite_noop (base : ByteArray) (dest len : ℕ) (h : base.size ≤ dest) :
    ByteArray.empty.write 0 base dest len = base := by
  unfold ByteArray.write
  by_cases hl : len = 0
  · simp only [hl, if_pos]
  · rw [if_neg hl, if_pos (show (0:ℕ) ≥ ByteArray.empty.size by rw [ByteArray.size_empty])]
    rw [show min len (base.size - dest) = 0 by omega, show min dest base.size = base.size by omega]
    apply ByteArray.ext
    have hb : base.data.size = base.size := rfl
    rw [ByteArray.data_copySlice, Array.extract_eq_self_of_le (le_of_eq hb),
      Array.extract_eq_empty_of_le
        (by omega : min 0 (ffi.ByteArray.zeroes { toBitVec := (↑(0:ℕ)) }).data.size ≤ 0 + 0),
      Array.extract_eq_empty_of_le
        (by rw [hb]; omega : min base.data.size base.data.size ≤
          base.size + min 0 ((ffi.ByteArray.zeroes { toBitVec := (↑(0:ℕ)) }).data.size - 0)),
      Array.append_empty, Array.append_empty]

theorem tlcCtorEvmCost0_mstore {s : State} {aw a b : UInt256} {t : List UInt256}
    (haws : s.machineState.activeWords = aw) (hstk : s.machineState.stack = a :: b :: t)
    (h : a.toNat + 32 ≤ 32 * aw.toNat) : memoryExpansionCost s .MSTORE = 0 := by
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk, List.getElem!_cons_zero]
  rw [tlcCtorEvmAwOut aw a.toNat 32 h]; omega

theorem tlcCtorEvmCost0_mload {s : State} {aw a : UInt256} {t : List UInt256}
    (haws : s.machineState.activeWords = aw) (hstk : s.machineState.stack = a :: t)
    (h : a.toNat + 32 ≤ 32 * aw.toNat) : memoryExpansionCost s .MLOAD = 0 := by
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk, List.getElem!_cons_zero]
  rw [tlcCtorEvmAwOut aw a.toNat 32 h]; omega

theorem tlcCtorEvmCost0_keccak {s : State} {aw a b : UInt256} {t : List UInt256}
    (haws : s.machineState.activeWords = aw) (hstk : s.machineState.stack = a :: b :: t)
    (h : a.toNat + b.toNat ≤ 32 * aw.toNat) : memoryExpansionCost s .KECCAK256 = 0 := by
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk, List.getElem!_cons_zero,
    List.getElem!_cons_succ]
  rw [tlcCtorEvmAwOut aw a.toNat b.toNat h]; omega

theorem tlcCtorEvmCost0_log4 {s : State} {aw a c d e f : UInt256} {t : List UInt256}
    (haws : s.machineState.activeWords = aw)
    (hstk : s.machineState.stack = a :: ⟨0⟩ :: c :: d :: e :: f :: t) :
    memoryExpansionCost s .LOG4 = 0 := by
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk, List.getElem!_cons_zero,
    List.getElem!_cons_succ]
  rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, tlcCtorEvmAwOut0 aw a.toNat]; omega

theorem tlcCtorEvmCost0_log1 {s : State} {aw a c : UInt256} {t : List UInt256}
    (haws : s.machineState.activeWords = aw)
    (hstk : s.machineState.stack = a :: ⟨0⟩ :: c :: t) :
    memoryExpansionCost s .LOG1 = 0 := by
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk, List.getElem!_cons_zero,
    List.getElem!_cons_succ]
  rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, tlcCtorEvmAwOut0 aw a.toNat]; omega

theorem tlcCtorInitcodeSuccess {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchCreationBytecode)
    (hperm : I.perm = true) (hcd : I.calldata = ByteArray.empty) :
    RDret timelockControllerBenchCreationBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, tlcCtorFinalMap I σ) timelockControllerBenchBytecode := by
  sorry

end OpenZeppelinBench.TimelockController
