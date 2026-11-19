import Benchmarks.Midnight.Interpolation
import Benchmarks.Midnight.CheckedArithmetic
import Benchmarks.Midnight.RuntimeBlocks_030
import Benchmarks.Midnight.RuntimeBlocks_082

/-! The shared bytecode suffix evaluating the settlement-fee interpolation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem settlementInterpolationTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {lower upper time start finish ret : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024)
    (hlower : lower.toNat < 2 ^ 64) (hupper : upper.toNat < 2 ^ 64)
    (hstart24 : start.toNat < 2 ^ 24) (hfinish : finish.toNat < 2 ^ 32)
    (hstart : start.toNat ≤ time.toNat) (htime : time.toNat ≤ finish.toNat)
    (hwidth : start.toNat < finish.toNat)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨21993⟩
      ([start, ⟨16777215⟩, ⟨22009⟩, finish, ⟨7530⟩, upper, ⟨22015⟩, time,
        ⟨22021⟩, ⟨4294967295⟩, ⟨22027⟩, lower, ⟨22033⟩, ret] ++ R)
      mem aw rdata σ k C) :
    ∃ k' C', RD midnightBytecode I g s0 ret
      (interpolatedFee lower upper time start finish :: R) mem aw rdata σ k' C' := by
  have hs : UInt256.land start ⟨16777215⟩ = start :=
    u256LandMaskCleanOfToNat start _ (by decide) hstart24
  have he : UInt256.land finish ⟨4294967295⟩ = finish :=
    u256LandMaskCleanOfToNat finish _ (by decide) hfinish
  obtain ⟨hleft, hright, hsum⟩ := interpolationBounds hlower hupper hfinish hstart htime
  have rd1 := midnightBlocks.midnight_block_21993
    (by simp; omega) (by native_decide) rd
  simp only [midnightBlocks.midnight_block_21993_stack, hs, he] at rd1
  obtain ⟨_, _, rd2⟩ := midnightCheckedSub (by simp; omega) htime (by native_decide) rd1
  have rd3 := midnightBlocks.midnight_block_7530 (by simp; omega) (by native_decide) rd2
  simp only [midnightBlocks.midnight_block_7530_stack] at rd3
  obtain ⟨_, _, rd4⟩ := midnightCheckedMul (by simp; omega) hleft (by native_decide) rd3
  have rd5 := midnightBlocks.midnight_block_22009 (by simp; omega) (by native_decide) rd4
  simp only [midnightBlocks.midnight_block_22009_stack] at rd5
  obtain ⟨_, _, rd6⟩ := midnightCheckedSub (by simp; omega) hstart (by native_decide) rd5
  have rd7 := midnightBlocks.midnight_block_7530 (by simp; omega) (by native_decide) rd6
  simp only [midnightBlocks.midnight_block_7530_stack] at rd7
  obtain ⟨_, _, rd8⟩ := midnightCheckedMul (by simp; omega) hright (by native_decide) rd7
  have rd9 := midnightBlocks.midnight_block_22015 (by simp; omega) (by native_decide) rd8
  simp only [midnightBlocks.midnight_block_22015_stack] at rd9
  obtain ⟨_, _, rd10⟩ := midnightCheckedAdd (by simp; omega) hsum (by native_decide) rd9
  have rd11 := midnightBlocks.midnight_block_22021 (by simp; omega) (by native_decide) rd10
  simp only [midnightBlocks.midnight_block_22021_stack] at rd11
  obtain ⟨_, _, rd12⟩ := midnightCheckedSub (by simp; omega) hwidth.le (by native_decide) rd11
  have rd13 := midnightBlocks.midnight_block_22027 (by simp; omega) (by native_decide) rd12
  simp only [midnightBlocks.midnight_block_22027_stack] at rd13
  have hnz : UInt256.sub finish start ≠ ⟨0⟩ := by
    intro hz
    have hn := congrArg UInt256.toNat hz
    rw [usub_toNat hwidth.le] at hn
    change finish.toNat - start.toNat = 0 at hn
    omega
  obtain ⟨_, _, rd14⟩ := midnightCheckedDiv (by simp; omega) hnz (by native_decide) rd13
  have rd15 := midnightBlocks.midnight_block_22033 (by simp; omega) hret rd14
  exact ⟨_, _, rd15⟩

end Benchmarks.Midnight
