import Benchmarks.Morpho.MorphoBlue.FlashLoanDecode
import Benchmarks.Morpho.MorphoBlue.FlashLoanMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def flashLoanGuardStack (cd : ByteArray) (R : List UInt256) : List UInt256 :=
  [calldataWord cd 4, solcAddrMask, calldataWord cd (4 + (calldataWord cd 68).toNat), UInt256.ofNat 0,
    calldataWord cd 36, (UInt256.ofNat 4 + calldataWord cd 68) + UInt256.ofNat 32, UInt256.ofNat 0] ++ R

theorem morphoFlashLoanPrepareGuard {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 20 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1033)
      (flashLoanDecodeStack ee.calldata R) solcFreePtrMem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12097)
      (UInt256.isZero (UInt256.isZero (calldataWord ee.calldata 36)) :: UInt256.ofNat 128 ::
        UInt256.ofNat 1055 :: flashLoanGuardStack ee.calldata R) flashLoanGuardMem aw' out σ k' C' := by
  have rd0 := morphoBlocks.morpho_block_1033 (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 9 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨a1, k1, C1, rd1⟩ := morphoZeroAssetsMessage (v := v)
    (by change R.length + 8 + 8 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest)
    (show memLoad (UInt256.ofNat 64) solcFreePtrMem = UInt256.ofNat 128 from solcFreePtrMem_mload64)
    (by decide) rd0
  have rd2 := morphoBlocks.morpho_block_1047 (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 9 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  exact ⟨a1, _, _, rd2⟩

theorem morphoFlashLoanGuardZero {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 20 ≤ 1024)
    (hz : calldataWord ee.calldata 36 = ⟨0⟩)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1033)
      (flashLoanDecodeStack ee.calldata R) solcFreePtrMem aw out σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoFlashLoanPrepareGuard hstack h
  refine morphoRequireFalseShort (by change R.length + 7 + 11 ≤ 1024; omega)
    (by rw [hz]; rfl) ?_ ?_ rd1
  · rw [flashLoanGuardMem_facts.2.2.2]; decide
  · rw [flashLoanGuardMem_facts.2.2.2]; decide

theorem morphoFlashLoanGuardOk {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 20 ≤ 1024)
    (hz : calldataWord ee.calldata 36 ≠ ⟨0⟩)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1033)
      (flashLoanDecodeStack ee.calldata R) solcFreePtrMem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1055)
      (flashLoanGuardStack ee.calldata R) flashLoanGuardMem aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoFlashLoanPrepareGuard hstack h
  obtain ⟨k2, C2, rd2⟩ := morphoRequireTrue (by change R.length + 7 + 4 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest)
    (by rw [isZero_eq_zero_of_ne hz]; rfl) rd1
  exact ⟨a1, k2, C2, rd2⟩

def flashLoanCallTail (cd : ByteArray) (R : List UInt256) : List UInt256 :=
  [(UInt256.ofNat 4 + calldataWord cd 68) + UInt256.ofNat 32,
    calldataWord cd (4 + (calldataWord cd 68).toNat), UInt256.ofNat 0,
    calldataWord cd 36, calldataWord cd 4, UInt256.ofNat 0] ++ R

theorem morphoFlashLoanEnter {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 20 ≤ 1024)
    (ha : (calldataWord ee.calldata 4).toNat < EVM.addressModulus) (hperm : ee.perm = true)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1055)
      (flashLoanGuardStack ee.calldata R) flashLoanGuardMem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14666)
      ([calldataWord ee.calldata 4, UInt256.ofNat ee.source.val, calldataWord ee.calldata 36, UInt256.ofNat 1113] ++
        flashLoanCallTail ee.calldata R) (flashLoanEnterMem (calldataWord ee.calldata 36)) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_1055_packed
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 10 ≤ 1024; omega) hperm
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [morphoBlocks.morpho_block_1055_stack, morphoBlocks.morpho_block_1055_memory] at rd1
  change RD _ _ _ _ _ ([_ , _, _, _, _, _, _, _, _, _] ++ R) _ _ _ _ _ _ at rd1
  rw [solcAddrMask_clean ha, flashLoanGuardMem_facts.2.1] at rd1
  exact ⟨a1, k1, C1, rd1⟩

end Benchmarks.Morpho.MorphoBlue
