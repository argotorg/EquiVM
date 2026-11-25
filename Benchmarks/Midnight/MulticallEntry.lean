import Benchmarks.Midnight.MulticallDecode
import Benchmarks.Midnight.CalldataSliceTrace
import Benchmarks.Midnight.RuntimeBlocks_016

variable {fork : Ethereum.Fork}

/-! The multicall entry guards and its outer calldata-array reference. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000

theorem midnightMulticallEntry {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024) (h4 : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hselector : (bytesToWord (I.calldata.toList.take 4)).toNat = 0xac9650d8)
    (rd : RD fork midnightBytecode I g s0 ⟨3548⟩ R mem aw rdata σ k C) :
    (config.externalABI.decodeCalldata? ["calls"] [.dynamicArray .bytes] I.calldata = none ∧
      RDrev fork midnightBytecode g s0) ∨
    (CalldataArgumentValid false I.calldata 4 ∧
      config.externalABI.decodeCalldata? ["calls"] [.dynamicArray .bytes] I.calldata =
        decodeMulticallArguments I.calldata ∧
      ∃ k' C', C ≤ C' ∧ RD fork midnightBytecode I g s0 ⟨3590⟩
        (calldataArgumentLength I.calldata 4 :: calldataArgumentPointer I.calldata 4 :: R)
        mem aw rdata σ k' C') := by
  have reject (hc : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size)
      ⟨32⟩ = ⟨1⟩) :
      config.externalABI.decodeCalldata? ["calls"] [.dynamicArray .bytes] I.calldata = none ∧
        RDrev fork midnightBytecode g s0 := by
    refine ⟨midnightDecodeMulticall_none_check h4 (solcSLT_sub4_of_check (bit := true) hc), ?_⟩
    have rr := midnightBlocks.midnight_block_3548_taken (by omega)
      (by change UInt256.slt (UInt256.lnot ⟨3⟩ + _) ⟨32⟩ ≠ ⟨0⟩
          rw [hc]; decide) (by jump_dest) rd
    exact midnightBlocks.midnight_block_712 (by omega) rr
  by_cases hshort : I.calldata.size < 36
  · exact Or.inl (reject (entrySizeCheck_short h4 hshort (by decide) hsize))
  by_cases hhuge : 2^255 + 4 ≤ I.calldata.size
  · exact Or.inl (reject (entrySizeCheck_huge hhuge hsize (by decide)))
  have h36 : 36 ≤ I.calldata.size := by omega
  have hcheck : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ = ⟨0⟩ :=
    entrySizeCheck_ok h36 (by omega) hsize
  have hdecode := midnightDecodeMulticall h36 hsize hselector
    (solcSLT_sub4_of_check (bit := false) hcheck)
  have rd1 := midnightBlocks.midnight_block_3548_fallthrough (by omega) hcheck rd
  by_cases ho : (calldataWord I.calldata 4).toNat < 2^64
  · have hc : UInt256.gt (calldataWord I.calldata 4)
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
          (UInt256.ofNat 1)) = ⟨0⟩ := ugt_zero (by change _ ≤ 2^64 - 1; omega)
    have rd2 := midnightBlocks.midnight_block_3560_fallthrough (by omega) hc rd1
    have rd3 := midnightBlocks.midnight_block_3577 (by omega) (by jump_dest) rd2
    have hh : (calldataArgumentHead I.calldata 4).toNat < 2^128 := by
      rw [calldataArgumentHead_toNat ho]
      omega
    rcases midnightCalldataSlice false hstack hsize hh (by jump_dest) rd3 with
      ⟨hbad, hrev⟩ | ⟨hv, k4, C4, hc4, rd4⟩
    · have hv : ¬ CalldataArgumentValid false I.calldata 4 := fun h ↦ hbad h.2
      exact Or.inl ⟨hdecode.trans (by simp only [decodeMulticallArguments, if_neg hv]), hrev⟩
    · exact Or.inr ⟨⟨ho, hv⟩, hdecode, k4, C4, by omega, rd4⟩
  · have hc : UInt256.gt (calldataWord I.calldata 4)
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
          (UInt256.ofNat 1)) ≠ ⟨0⟩ := by
      rw [ugt_one (by change 2^64 - 1 < _; omega)]
      decide
    have rr := midnightBlocks.midnight_block_3560_taken (by omega) hc (by jump_dest) rd1
    have hv : ¬ CalldataArgumentValid false I.calldata 4 := fun h ↦ ho h.1
    exact Or.inl ⟨hdecode.trans (by simp only [decodeMulticallArguments, if_neg hv]),
      midnightBlocks.midnight_block_712 (by change R.length + 1 + 2 ≤ 1024; omega) rr⟩

theorem wordAddLnot30 (a : UInt256) :
    a + UInt256.lnot (UInt256.ofNat 30) = UInt256.sub a (UInt256.ofNat 31) := by
  apply u256_inj
  have ha := a.val.isLt
  change a.toNat < UInt256.size at ha
  have hm : (UInt256.lnot (UInt256.ofNat 30)).toNat = 2^256 - 31 := by decide +kernel
  rw [uadd_toNat, hm]
  by_cases hb : 31 ≤ a.toNat
  · rw [usub_toNat (a := a) (b := UInt256.ofNat 31) (by exact hb)]
    simp only [show (UInt256.ofNat 31).toNat = 31 from rfl, UInt256.size] at ha ⊢
    omega
  · rw [usub_toNat_underflow (a := a) (b := UInt256.ofNat 31) (by exact Nat.lt_of_not_ge hb)]
    simp only [show (UInt256.ofNat 31).toNat = 31 from rfl, UInt256.size]
    omega

end Benchmarks.Midnight
