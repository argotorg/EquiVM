import Benchmarks.OpenZeppelinBench.TimelockController.Return

/-!
# OpenZeppelin TimelockController shared mapping-getter routines

Two reusable `RD` routines factored out of the `getTimestamp(bytes32)` refinement:

* `tlcMappingGetSlot1` — the inline `mapping(bytes32 => uint256)` slot getter at base slot `1`
  (PUSH0-based Shanghai scratch write `key‖1`, `KECCAK256`, `SLOAD`), generic over the mapping key
  and the return continuation.  The keccak preimage lives in `twoWordHashMem key ⟨1⟩ solcFreePtrMem`.
* `tlcReturnWordFromMem` — the split 32-byte return encoder of `Return.tlcReturnWord`, generalized to
  any free-pointer-preserving scratch memory (`size = 96`, `mem[0x40] = 0x80`).  A mapping getter
  dirties the `[0,0x40)` scratch, so the return runs over `twoWordHashMem …`, not `solcFreePtrMem`.

LIBRARY CANDIDATEs: `Reasoning.Solc` — `tlcMappingGetSlot1` generalizes the base-slot-`0`
`RD.solcZeroSlotMappingGetter` to base slot `1` with the modern PUSH0 write order; and
`tlcReturnWordFromMem` is the memory-generic form of the split return encoder.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace OpenZeppelinBench.TimelockController

/-! ## Mapping-slot keccak identity for the modern (key-first) scratch layout -/

/-- The slot word an EVM `KECCAK256` over `twoWordHashMem key baseSlot solcFreePtrMem` (key at
    `mem[0]`, `baseSlot` at `mem[0x20]`) pushes equals the Solm layout mapping slot for
    `mapping[key]` at `baseSlot`.  (Analogue of `solcMappingKeccakSlot`, whose scratch writes the
    slot first; solc 0.8.35 writes the key first.) -/
theorem tlcTwoWordKeccakSlot (baseSlot key : UInt256) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key baseSlot solcFreePtrMem).readWithPadding 0 64)))
      = solcMappingSlot baseSlot key := by
  rw [twoWordHashMem_read0_64 key baseSlot solcFreePtrMem_size]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot

/-! ## Base-slot-1 mapping getter (@1333 in the TimelockController runtime)

    Stack at entry `[key, ret, R]`; the routine writes `key‖1` into scratch, hashes, loads the slot,
    and `JUMP`s to `ret` leaving `[slotWord, R]`.  Memory becomes `twoWordHashMem key ⟨1⟩ …`. -/

-- LIBRARY CANDIDATE: `Reasoning.Solc` — base-slot-`1` PUSH0 mapping getter (key-first scratch write).
theorem tlcMappingGetSlot1 {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {key ret : UInt256} {R : List UInt256} {rdata : ByteArray} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode ee g s0 ⟨1333⟩ (key :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hret : (D_J timelockControllerBenchBytecode 0).contains ret = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD timelockControllerBenchBytecode ee g s0 ret
      (solcSlotWord σ ee (solcMappingSlot ⟨1⟩ key) :: R)
      (twoWordHashMem key ⟨1⟩ solcFreePtrMem) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  have hk := h.jumpdest (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.mstore 0 (wordAt0Mem key solcFreePtrMem) (UInt256.ofNat 3) (by native_decide) mem_cost
        (by rfl) (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
    |>.mstore 0 (twoWordHashMem key ⟨1⟩ solcFreePtrMem) (UInt256.ofNat 3) (by native_decide) mem_cost
        (by rfl) (by native_decide) (by evm_ov)
    |>.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.keccak256 0 (solcMappingSlot ⟨1⟩ key) (UInt256.ofNat 3) (by native_decide) mem_cost
        (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
            exact tlcTwoWordKeccakSlot ⟨1⟩ key)
        (by native_decide) (by evm_ov)
  obtain ⟨_, _, hsl⟩ := hk.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, hsl.swap1 (by native_decide) (by evm_ov) |>.jump (by native_decide) hret (by evm_ov)⟩

/-! ## Memory-generic split 32-byte return encoder (from pc 581)

    `Return.tlcReturnWord` bakes in `solcFreePtrMem`; a mapping getter leaves the free pointer intact
    at `mem[0x40]` but dirties the `[0,0x40)` scratch, so we need the return over any such memory. -/

/-- Memory after the return epilogue stores the 32-byte word `val` at the free pointer `0x80`. -/
def tlcRetMem (mem : ByteArray) (val : UInt256) : ByteArray :=
  (UInt256.toByteArray val).write 0 mem 128 32

theorem tlcRetMem_eq {mem : ByteArray} (hsize : mem.size = 96) (val : UInt256) :
    tlcRetMem mem val
      = (mem ++ ffi.ByteArray.zeroes (USize.ofNat 32)) ++ UInt256.toByteArray val := by
  rw [tlcRetMem, toByteArray_write_eq _ _ _ (by rw [hsize]; omega)
      (by rw [hsize]; exact lt_usize _ (by norm_num))]
  norm_num [hsize]

theorem tlcRetMem_size {mem : ByteArray} (hsize : mem.size = 96) (val : UInt256) :
    (tlcRetMem mem val).size = 160 := by
  rw [tlcRetMem_eq hsize, ByteArray.size_append, ByteArray.size_append, hsize,
      zeroes_ofNat_size _ (by norm_num), toByteArray_size]

theorem tlcRetMem_read64 {mem : ByteArray} (hsize : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) (val : UInt256) :
    (tlcRetMem mem val).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [readWithPadding_eq_extract _ _ (by rw [tlcRetMem_size hsize]; omega), tlcRetMem_eq hsize,
      extract_append_left _ _ _ _
        (by rw [ByteArray.size_append, hsize, zeroes_ofNat_size _ (by norm_num)]; omega),
      extract_append_left _ _ _ _ (by rw [hsize]),
      ← readWithPadding_eq_extract _ _ (by rw [hsize]), hread64]

theorem tlcRetMem_read128 {mem : ByteArray} (hsize : mem.size = 96) (val : UInt256) :
    (tlcRetMem mem val).readWithPadding 128 32 = UInt256.toByteArray val := by
  have hpad : (mem ++ ffi.ByteArray.zeroes (USize.ofNat 32)).size = 128 := by
    rw [ByteArray.size_append, hsize, zeroes_ofNat_size _ (by norm_num)]
  rw [readWithPadding_eq_extract _ _ (by have := tlcRetMem_size hsize val; omega), tlcRetMem_eq hsize,
      extract_append_right' _ _ _ _ (by omega) (by have := toByteArray_size val; omega)]

theorem tlcRetMem_mload64 {mem : ByteArray} (hsize : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) (val : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (tlcRetMem mem val).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((tlcRetMem mem val).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [tlcRetMem_size hsize]; decide) (by decide)
    (tlcRetMem_read64 hsize hread64 val)

-- LIBRARY CANDIDATE: `Reasoning.Solc` — memory-generic split-encoder analogue of `tlcReturnWord`.
theorem tlcReturnWordFromMem {cA gh bl σ σ₀ A I} {g : Sat256} {val cont : UInt256} {R : List UInt256}
    {mem : ByteArray} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨581⟩
      (val :: cont :: R) mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsize : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 5 ≤ 1024) :
    RDret timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray val) := by
  have h521 := h.jumpdest (by native_decide) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨64⟩ (by native_decide) (by simp only [List.length_cons]; omega)
    |>.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
        (mloadFreePtrValue (by rw [hsize]; decide) (by decide) hread64) (by decide) (by evm_ov)
    |>.swap1 (by native_decide) (by simp only [List.length_cons]; omega)
    |>.dup2 (by native_decide) (by simp only [List.length_cons]; omega)
    |>.mstore 6 (tlcRetMem mem val) (UInt256.ofNat 5) (by native_decide) mem_cost
        (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl) (by decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by simp only [List.length_cons]; omega)
    |>.add (by native_decide) (by simp only [List.length_cons]; omega)
    |>.push2 ⟨521⟩ (by native_decide) (by simp only [List.length_cons]; omega)
    |>.jump (by native_decide) (by jump_dest) (by simp only [List.length_cons]; omega)
  have hret := h521.jumpdest (by native_decide) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨64⟩ (by native_decide) (by simp only [List.length_cons]; omega)
    |>.mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide) mem_cost
        (tlcRetMem_mload64 hsize hread64 val) (by decide) (by evm_ov)
    |>.dup1 (by native_decide) (by simp only [List.length_cons]; omega)
    |>.swap2 (by native_decide) (by simp only [List.length_cons]; omega)
    |>.sub (by native_decide) (by simp only [List.length_cons]; omega)
    |>.swap1 (by native_decide) (by simp only [List.length_cons]; omega)
  exact hret.ret 0 (UInt256.toByteArray val) (by native_decide) mem_cost
    (by rw [show ((⟨32⟩ + ⟨128⟩ : UInt256).sub ⟨128⟩).toNat = 32 from by decide,
        show (⟨128⟩ : UInt256).toNat = 128 from by decide]; exact tlcRetMem_read128 hsize val)
    (by simp only [List.length_cons]; omega)

end OpenZeppelinBench.TimelockController
