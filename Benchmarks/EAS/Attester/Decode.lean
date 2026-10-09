import Benchmarks.EAS.Attester.Common
import Benchmarks.EAS.Attester.ABIHelpers

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

theorem attesterDecodeTwoWords {words : String → UInt256} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (h : RD (immutableLayout.runtime attesterBytecode words) ee g s0 ⟨2662⟩
      (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata σ k C)
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J (immutableLayout.runtime attesterBytecode words) 0).contains ret = true)
    (hlen : 68 ≤ ee.calldata.size) (hhi : ee.calldata.size < 2 ^ 255 + 4)
    (hsize : ee.calldata.size < UInt256.size) :
    ∃ k' C', RD (immutableLayout.runtime attesterBytecode words) ee g s0 ret
      (calldataWord ee.calldata 36 :: calldataWord ee.calldata 4 :: R) mem aw rdata σ k' C' := by
  have rd2681 := attesterRuntime_block_2662_taken (by simp only [List.length_cons]; omega)
    (by change UInt256.isZero (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size)
          ⟨4⟩) ⟨64⟩) ≠ ⟨0⟩
        rw [solcDecodeLenCheckOk_4_64 hlen hhi hsize]; decide)
    (by rw [attesterRuntime_validJumps]; native_decide) h
  have rdRet := attesterRuntime_block_2681 (by omega) hvalid rd2681
  exact ⟨_, _, rdRet⟩

theorem attesterDecodeTwoWordsRevert {words : String → UInt256} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (h : RD (immutableLayout.runtime attesterBytecode words) ee g s0 ⟨2662⟩
      (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: R) mem aw rdata σ k C)
    (hstack : R.length + 7 ≤ 1024) (hsz : 4 ≤ ee.calldata.size)
    (hsize : ee.calldata.size < UInt256.size)
    (hbad : ee.calldata.size < 68 ∨ 2 ^ 255 + 4 ≤ ee.calldata.size) :
    RDrev (immutableLayout.runtime attesterBytecode words) g s0 := by
  have hlen : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    rcases hbad with hshort | hhi
    · exact solcDecodeLenCheckShort_4_64 hsz hshort hsize
    · exact solcDecodeLenCheckHuge_4_64 hhi hsize
  have rd2677 := attesterRuntime_block_2662_fallthrough hstack
    (by change UInt256.isZero (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size)
          ⟨4⟩) ⟨64⟩) = ⟨0⟩
        rw [hlen]; rfl) h
  exact attesterRuntime_block_2677
    (by simp only [attesterRuntime_block_2662_fallthrough_stack, List.length_cons]; omega) rd2677

end Benchmarks.EAS.Attester
