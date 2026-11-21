import Benchmarks.Midnight.LiquidateCallbackCollateralStep
import Benchmarks.Midnight.CollateralDecodeCons
import Benchmarks.Midnight.CollateralLoopMemory

/-! All collateral records copied into liquidation's callback calldata. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightLiquidateCallbackCollateralLoop {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw index base ptr a b c d output root badDebt : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (cs : List CollateralData)
    (hstack : R.length + 24 ≤ 1024)
    (hcount : (calldataWord I.calldata (base + UInt256.ofNat 4).toNat).toNat = index.toNat + cs.length)
    (hptr : ptr.toNat + 128 * cs.length < UInt256.size)
    (hout : output.toNat + 128 * cs.length < UInt256.size)
    (hd : decodeCollateralElements cs.length I.calldata ptr.toNat = some cs)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨6038⟩
      ([index, base, ptr, a, b, c, d, output, root, badDebt, root] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', C ≤ C' ∧
      MemoryFunding credit (writeWordArray mem output.toNat (cs.flatMap CollateralData.words))
        aw' C' ∧
      RD midnightBytecode I g s0 ⟨6050⟩
        ([index + UInt256.ofNat cs.length, base, ptr + UInt256.ofNat (128 * cs.length),
          a, b, c, d, output + UInt256.ofNat (128 * cs.length), root, badDebt, root] ++ R)
        (writeWordArray mem output.toNat (cs.flatMap CollateralData.words)) aw' rdata σ k' C' := by
  induction cs generalizing mem aw index ptr output k C with
  | nil =>
    have hc : UInt256.lt index (calldataWord I.calldata (base + UInt256.ofNat 4).toNat) = ⟨0⟩ :=
      ult_zero (by simpa only [List.length_nil, Nat.add_zero] using hcount.le)
    have rd1 := midnightBlocks.midnight_block_6038_fallthrough
      (R := [ptr, a, b, c, d, output, root, badDebt, root] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hc rd
    refine ⟨aw, k + 9, C + 32, by omega, ?_⟩
    simpa only [List.flatMap_nil, writeWordArray, List.length_nil, Nat.mul_zero,
      wordAddNat_zero] using And.intro (ha.mono (by omega) : MemoryFunding credit mem aw (C + 32)) rd1
  | cons item cs ih =>
    obtain ⟨_, hcanon, hitem, htail⟩ := decodeCollateralElements_cons hd
    have hc : UInt256.lt index (calldataWord I.calldata (base + UInt256.ofNat 4).toNat) = ⟨1⟩ :=
      ult_one (by simp only [List.length_cons] at hcount; omega)
    have rd1 := midnightBlocks.midnight_block_6038_taken
      (R := [ptr, a, b, c, d, output, root, badDebt, root] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      (by change UInt256.lt index (calldataWord I.calldata (base + UInt256.ofNat 4).toNat) ≠ ⟨0⟩
          rw [hc]; decide) (by jump_dest) rd
    obtain ⟨aw2, k2, C2, hc2, ha2, rd2⟩ := midnightLiquidateCallbackCollateralStep hstack
      (by simp only [List.length_cons] at hptr; omega)
      (by simp only [List.length_cons] at hout; omega) hcanon (ha.mono (by omega)) rd1
    rw [← hitem] at ha2 rd2
    have hi : (index + UInt256.ofNat 1).toNat = index.toNat + 1 :=
      uadd_word_ofNat_toNat _ _ (by
        have hlt : (calldataWord I.calldata (base + UInt256.ofNat 4).toNat).toNat < UInt256.size :=
          (calldataWord I.calldata (base + UInt256.ofNat 4).toNat).val.isLt
        simp only [List.length_cons] at hcount
        omega)
    have hp : (ptr + UInt256.ofNat 128).toNat = ptr.toNat + 128 :=
      uadd_word_ofNat_toNat _ _ (by simp only [List.length_cons] at hptr; omega)
    have ho : (output + UInt256.ofNat 128).toNat = output.toNat + 128 :=
      uadd_word_ofNat_toNat _ _ (by simp only [List.length_cons] at hout; omega)
    obtain ⟨aw3, k3, C3, hc3, ha3, rd3⟩ := ih
      (by rw [hi]; simp only [List.length_cons] at hcount; omega)
      (by rw [hp]; simp only [List.length_cons] at hptr; omega)
      (by rw [ho]; simp only [List.length_cons] at hout; omega)
      (by rw [hp]; exact htail) ha2 rd2
    have hm : writeWordArray (writeWordArray mem output.toNat item.words)
        (output + UInt256.ofNat 128).toNat (cs.flatMap CollateralData.words) =
        writeWordArray mem output.toNat ((item :: cs).flatMap CollateralData.words) := by
      rw [List.flatMap_cons, writeWordArray_append, ho]
      rfl
    rw [hm] at ha3 rd3
    refine ⟨aw3, k3, C3, by omega, ha3, ?_⟩
    simpa only [List.length_cons, wordAddNat_add,
      show 1 + cs.length = cs.length + 1 by omega,
      show 128 + 128 * cs.length = 128 * (cs.length + 1) by omega] using rd3

end Benchmarks.Midnight
