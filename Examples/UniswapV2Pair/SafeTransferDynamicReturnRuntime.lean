import Examples.UniswapV2Pair.SafeTransferDynamicCallRuntime
import Examples.UniswapV2Pair.ReturnDataMemory
import Examples.UniswapV2Pair.SafeTransferEmptyReturnCore

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferDynamicEmptyReturnToRet
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {base out : ByteArray} {ptr aw value toWord token ret : UInt256} {R : List UInt256} {k C : Nat}
    (rd6595 : RD uniswapV2PairBytecode I g s0 ⟨6595⟩
      (⟨1⟩ :: (ptr + ⟨232⟩) :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ :: value :: toWord :: token :: ret :: R)
      (safeTransferDynamicCallMem2 base ptr toWord value) (safeTransferDynamicCallWords2 aw ptr) out acc k C)
    (hout : out.size = 0) (hin : 128 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size)
    (hptrLo : 128 ≤ ptr.toNat) (haw : aw.toNat * 32 < UInt256.size) (hptr : ptr.toNat + 291 < UInt256.size)
    (hzero : base.readWithPadding 96 32 = (⟨0⟩ : UInt256).toByteArray)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true) (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ret R
      (safeTransferDynamicCallMem2 base ptr toWord value) (safeTransferDynamicCallWords2 aw ptr) out acc k' C' := by
  exact RD.uniswapSafeTransferDynamicEmptyReturnToRet_of_zeroSlot rd6595 hout (by omega)
    hgap hptrLo haw hptr
    ((safeTransferDynamicCallMem2_read96 ptr toWord value hin hgap hptrLo (by omega)).trans hzero)
    hret hov

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferNonemptyReturnStored
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem out : ByteArray} {ptr aw status callRet maskedToken value toWord token ret : UInt256}
    {R : List UInt256} {k C : Nat}
    (rd6595 : RD uniswapV2PairBytecode I g s0 ⟨6595⟩
      (status :: callRet :: maskedToken :: ⟨96⟩ :: ⟨0⟩ :: value :: toWord :: token :: ret :: R)
      mem aw out acc k C)
    (houtNe : out.size ≠ 0) (hout : out.size < 2 ^ 255)
    (hload : memoryWordLoad mem aw ⟨64⟩ = ptr)
    (hptrLo : 96 ≤ ptr.toNat) (haw : aw.toNat * 32 < UInt256.size)
    (hcover : ptr.toNat + 64 ≤ aw.toNat * 32) (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨6652⟩ (ptr :: status :: value :: toWord :: token :: ret :: R)
      (solcReturnDataMem mem ptr out) (solcReturnDataActiveWords aw ptr out) out acc k' C' := by
  have haw64 : UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32) = aw :=
    UInt256_M_same_of_cover _ _ haw (by change 64 + 32 ≤ _; omega)
  have hawPtr : UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32) = aw :=
    UInt256_M_same_of_cover _ _ haw (by omega)
  exact RD.uniswapSafeTransferReturnNonemptyReturnToCheck rd6595 houtNe hout hload haw64 hawPtr rfl rfl hov

set_option maxHeartbeats 1000000 in
theorem uniswapSafeTransferNonemptyReturnRuntimeCases
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem out : ByteArray} {ptr aw callRet maskedToken value toWord token ret : UInt256} {z : Bool}
    {R : List UInt256} {k C : Nat}
    (rd6595 : RD uniswapV2PairBytecode I g s0 ⟨6595⟩
      ((if z then ⟨1⟩ else ⟨0⟩) :: callRet :: maskedToken :: ⟨96⟩ :: ⟨0⟩ :: value :: toWord :: token :: ret :: R)
      mem aw out acc k C)
    (houtNe : out.size ≠ 0) (hout : out.size < 2 ^ 255)
    (hload : memoryWordLoad mem aw ⟨64⟩ = ptr)
    (hin : 96 ≤ mem.size) (hptr : ptr.toNat + 32 ≤ mem.size)
    (hptrLo : 96 ≤ ptr.toNat) (haw : aw.toNat * 32 < UInt256.size)
    (hcover : ptr.toNat + 64 ≤ aw.toNat * 32) (hfit : ptr.toNat + out.size + 95 < UInt256.size)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true) (hov : R.length + 16 ≤ 1024) :
    ((z = false ∨ out.size < 32 ∨ UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) = ⟨0⟩) ∧
      RDrev uniswapV2PairBytecode g s0) ∨
    (z = true ∧ 32 ≤ out.size ∧ UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) ≠ ⟨0⟩ ∧
      ∃ k' C', RD uniswapV2PairBytecode I g s0 ret R
        (solcReturnDataMem mem ptr out) (solcReturnDataActiveWords aw ptr out) out acc k' C') := by
  obtain ⟨_, _, rd6652⟩ := RD.uniswapSafeTransferNonemptyReturnStored rd6595 houtNe hout hload hptrLo haw hcover hov
  cases hz : z with
  | false =>
    rw [hz] at rd6652
    exact Or.inl ⟨Or.inl rfl, RD.uniswapSafeTransferReturnNonemptyFailureReverts rd6652 hov⟩
  | true =>
    rw [hz] at rd6652
    obtain ⟨hloadSize, hawSize⟩ := solcReturnDataMem_mload_size aw ptr out hin hptr hcover haw hfit
    obtain ⟨_, _, rd6676⟩ := RD.uniswapSafeTransferReturnNonemptyTrueStatusToLengthLoaded
      (retPtr := ptr + ⟨32⟩) rd6652 houtNe hout hloadSize hawSize (u256_add_comm _ _) hov
    by_cases hs : out.size < 32
    · exact Or.inl ⟨Or.inr (Or.inl hs), RD.uniswapSafeTransferReturnNonemptyShortReverts rd6676 hs hout
        (by simp only [List.length_cons]; omega)⟩
    · have hout32 : 32 ≤ out.size := by omega
      obtain ⟨hloadWord, hawWord⟩ := solcReturnDataMem_mload_word aw ptr out hin hptr hcover haw hfit hout32
      by_cases hw : UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) = ⟨0⟩
      · exact Or.inl ⟨Or.inr (Or.inr hw), RD.uniswapSafeTransferReturnNonemptyFalseReverts rd6676 hout32 hout
          hw hloadWord hawWord hov⟩
      · exact Or.inr ⟨rfl, hout32, hw, RD.uniswapSafeTransferReturnNonemptyTrueToRet rd6676 hout32 hout
          hw hloadWord hawWord hret hov⟩

end UniswapV2Pair
