import Benchmarks.WETH9.ConstructorClear
import Reasoning.Memory

/-!
# WETH9 constructor — the reusable compact-string store subroutine (creation.hex pc 122–276)

`weth9StringStoreSubroutine` runs the shared subroutine that decodes the old compact-string length,
stores the short word at `slot`, and clears the stale keccak-data words, returning to `retAddr` with
`[slot]`.  It is invoked twice by the creation code (for `name` at slot 0 and `symbol` at slot 1).
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.WETH9

set_option maxRecDepth 4000000
set_option maxHeartbeats 6000000

/-! ## Active-words and memory-cost helpers (abstract active-words `aw`) -/

theorem weth9AwM0_eq (aw : UInt256) (h : 1 ≤ aw.toNat) :
    UInt256.ofNat (MachineState.M aw.toNat 0 32) = aw := by
  apply u256_inj
  have hM : MachineState.M aw.toNat 0 32 = aw.toNat := by
    simp only [MachineState.M]; change max aw.toNat 1 = aw.toNat; exact max_eq_left h
  rw [hM]; exact congrArg UInt256.toNat (u256_ofNat_toNat aw)

theorem weth9AwMemPtr_eq (aw : UInt256) (memPtr : Nat)
    (h : memPtr + 32 ≤ aw.toNat * 32) :
    UInt256.ofNat (MachineState.M aw.toNat memPtr 32) = aw := by
  apply u256_inj
  have hM : MachineState.M aw.toNat memPtr 32 = aw.toNat := by
    simp only [MachineState.M]
    rw [max_eq_left]
    omega
  rw [hM]; exact congrArg UInt256.toNat (u256_ofNat_toNat aw)

theorem weth9KeccakCost {aw off size : UInt256} {stk : List UInt256} :
    ∀ s : State, s.machineState.activeWords = aw →
      s.machineState.stack = off :: size :: stk →
      memoryExpansionCost s .KECCAK256 =
        Cₘ (UInt256.ofNat (MachineState.M aw.toNat off.toNat size.toNat)) - Cₘ aw := by
  intro s haw hstk
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk, haw, List.getElem!_cons_zero,
    List.getElem!_cons_succ]

theorem weth9MloadCost {aw off : UInt256} {stk : List UInt256} :
    ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = off :: stk →
      memoryExpansionCost s .MLOAD =
        Cₘ (UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)) - Cₘ aw := by
  intro s haw hstk
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk, haw, List.getElem!_cons_zero]

/-! ## The computed old-word count equals the Solm `solidityBytesDataWordCount` -/

theorem weth9OldWordsWord_eq (S : UInt256) :
    UInt256.div ((⟨31⟩ : UInt256) +
        UInt256.div (UInt256.land
          (UInt256.sub (UInt256.mul ⟨256⟩ (UInt256.isZero (UInt256.land ⟨1⟩ S))) ⟨1⟩) S) ⟨2⟩) ⟨32⟩ =
      UInt256.ofNat (solidityBytesDataWordCount (weth9DecodeLenWord S).toNat) := by
  rw [show UInt256.div (UInt256.land
      (UInt256.sub (UInt256.mul ⟨256⟩ (UInt256.isZero (UInt256.land ⟨1⟩ S))) ⟨1⟩) S) ⟨2⟩
      = weth9EvmLenWord S from rfl, weth9EvmLenWord_eq]
  apply u256_inj
  have hlt := weth9DecodeLenWord_lt S
  have hsize : UInt256.size = 2 ^ 256 := rfl
  rw [udiv_toNat, uadd_toNat,
    show (⟨31⟩ : UInt256).toNat = 31 from rfl, show (⟨32⟩ : UInt256).toNat = 32 from rfl,
    Nat.mod_eq_of_lt (by omega : 31 + (weth9DecodeLenWord S).toNat < UInt256.size)]
  unfold solidityBytesDataWordCount
  rw [ulit_toNat' _ (by omega : ((weth9DecodeLenWord S).toNat + 31) / 32 < UInt256.size)]
  omega

/-! ## The compact-string store subroutine (pc 122 → retAddr) -/

/-- The reusable store subroutine.  Entered at `⟨122⟩` with `[len, memPtr, slot, retAddr]`, the
    data word left-aligned at `mem[memPtr]`, and pre-allocated active words; returns to `retAddr`
    with `[slot]`, having stored the short word and cleared the stale keccak-data words. -/
theorem weth9StringStoreSubroutine
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (len memPtr slot retAddr dataword : UInt256)
    (hslot : slot = ⟨0⟩ ∨ slot = ⟨1⟩)
    (hlen : len.toNat < 31)
    (hperm : ee.perm = true)
    (hRA : (D_J weth9CreationBytecode 0).contains retAddr = true)
    (hmemPtr32 : 32 ≤ memPtr.toNat)
    (hmemSize : memPtr.toNat + 32 ≤ mem.size)
    (hawMem : memPtr.toNat + 32 ≤ aw.toNat * 32)
    (hawNoWrap : aw.toNat * 32 < UInt256.size)
    (haw1 : 1 ≤ aw.toNat)
    (hmemData : mem.readWithPadding memPtr.toNat 32 = UInt256.toByteArray dataword)
    (h : RD weth9CreationBytecode ee g s0 ⟨122⟩ [len, memPtr, slot, retAddr]
          mem aw rdata (cA, σ) k C) :
    ∃ k' C',
      RD weth9CreationBytecode ee g s0 retAddr [slot]
        (UInt256.toByteArray slot |>.write 0 mem 0 32) aw rdata
        (cA, clearDataWordsForwardFrom ee.codeOwner
          (sstoreAccountMap ee.codeOwner σ slot
            (UInt256.lor (len + len) (UInt256.land (UInt256.lnot ⟨255⟩) dataword)))
          (Solm.solidityBytesDataBaseSlot slot) ⟨0⟩
          (solidityBytesDataWordCount
            (weth9DecodeLenWord
              (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD slot ⟨0⟩))).toNat))
        k' C' := by
  -- abbreviations
  set S : UInt256 :=
    σ.find? ee.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD slot ⟨0⟩) with hSdef
  set mem1 : ByteArray := UInt256.toByteArray slot |>.write 0 mem 0 32 with hmem1def
  set ow : Nat := solidityBytesDataWordCount (weth9DecodeLenWord S).toNat with howdef
  set K : UInt256 := Solm.solidityBytesDataBaseSlot slot with hKdef
  set V : UInt256 :=
    UInt256.lor (len + len) (UInt256.land (UInt256.lnot ⟨255⟩) dataword) with hVdef
  -- Phase A: SLOAD the old header.
  have hA := evm_run h with [jumpdest, dup3, dup1]
  obtain ⟨_, _, hSload⟩ := hA.sload (by native_decide) (by evm_ov)
  -- Phase B: decode the old length; MSTORE the slot at mem[0].
  have hB := evm_run hSload with [
    push1 ⟨1⟩, dup2, push1 ⟨1⟩, and, iszero, push2 ⟨256⟩, mul, sub, and, push1 ⟨2⟩, swap1, div,
    swap1, push1 ⟨0⟩]
  have hMstore := hB.mstore
    (Cₘ (UInt256.ofNat (MachineState.M aw.toNat 0 32)) - Cₘ aw) mem1 aw
    (by native_decide)
    (fun s haws hstks => by
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
        List.getElem!_cons_zero, show (⟨0⟩ : UInt256).toNat = 0 from rfl])
    rfl (weth9AwM0_eq aw haw1) (by evm_ov)
  -- Phase C: KECCAK256(0,32) = keccak(slot).
  have hC := evm_run hMstore with [push1 ⟨32⟩, push1 ⟨0⟩]
  have hKecc := hC.keccak256
    (Cₘ (UInt256.ofNat (MachineState.M aw.toNat 0 32)) - Cₘ aw) K aw
    (by native_decide) weth9KeccakCost
    (by
      rw [show mem1.readWithPadding (⟨0⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat
            = UInt256.toByteArray slot from by
          rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, show (⟨32⟩ : UInt256).toNat = 32 from rfl,
            hmem1def, write32_read_back (UInt256.toByteArray slot) mem 0 (by rw [toByteArray_size])
              (by omega), toByteArray_extract_all]]
      rw [hKdef, Solm.solidityBytesDataBaseSlot]
      exact keccakSlot_eq _)
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl]; exact weth9AwM0_eq aw haw1)
    (by evm_ov)
  -- Phase D: compute oldWords, take the SHORT branch, MLOAD the data word.
  have hcondBranch : UInt256.lt ⟨31⟩ len = ⟨0⟩ :=
    ult_zero (by rw [show (⟨31⟩ : UInt256).toNat = 31 from rfl]; omega)
  have hD := evm_run hKecc with [
    swap1, push1 ⟨31⟩, add, push1 ⟨32⟩, swap1, div, dup2, add, swap3, dup3, push1 ⟨31⟩, lt,
    push2 ⟨187⟩, jumpiNT hcondBranch, dup1]
  have hMload := hD.mload
    (Cₘ (UInt256.ofNat (MachineState.M aw.toNat memPtr.toNat 32)) - Cₘ aw) dataword aw
    (by native_decide) weth9MloadCost
    (by
      refine mloadWordValue_of_readWithPadding (mem := mem1) (aw := aw) (off := memPtr)
        (v := dataword) ?_ ?_ ?_
      · rw [hmem1def, toByteArray_write32_size_of_le mem slot 0 mem.size (max mem.size 32)
          rfl (by omega) rfl]
        omega
      · intro hbad
        have hle : memPtr.toNat ≥ (aw * (⟨32⟩ : UInt256)).toNat := hbad
        rw [show (aw * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 from by
          simpa [show (⟨32⟩ : UInt256).toNat = 32 from rfl] using umul_toNat aw ⟨32⟩ hawNoWrap] at hle
        omega
      · rw [hmem1def, write32_read_above (UInt256.toByteArray slot) mem 0 memPtr.toNat
          (by rw [toByteArray_size]) (by omega) (by omega) (by omega)]
        exact hmemData)
    (weth9AwMemPtr_eq aw memPtr.toNat hawMem) (by evm_ov)
  -- Phase E: build the short word, SSTORE it at `slot`.
  have hE := evm_run hMload with [push1 ⟨255⟩, not, and, dup4, dup1, add, lor, dup6]
  obtain ⟨_, _, hSstore⟩ := hE.sstore hperm (by native_decide) (by evm_ov)
  -- Phase F: return-dance setup to the clear-loop head ⟨254⟩.
  have hF := evm_run hSstore with [
    push2 ⟨232⟩, jump (by native_decide),
    jumpdest, pop, push2 ⟨244⟩, swap3, swap2, pop, push2 ⟨248⟩, jump (by native_decide),
    jumpdest, push2 ⟨274⟩, swap2, swap1]
  -- Match the loop-head cursor to `K + ofNat ow` and run the loop + return dance.
  rw [weth9OldWordsWord_eq] at hF
  exact weth9ClearLoopAndReturn (σ' := sstoreAccountMap ee.codeOwner σ slot V)
    K ow slot retAddr (weth9NoOverflow slot hslot S) hperm hRA hF

end Benchmarks.WETH9
