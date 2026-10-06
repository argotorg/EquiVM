import Reasoning.MemoryArithmetic
import Examples.UniswapV2Pair.SkimSafeTransferReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## Dynamic `_safeTransfer` return-data tails -/


set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSafeTransferNonemptyHugeReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord token token1 ret sel status : UInt256}
    {o out : ByteArray} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (status :: ⟨360⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token1 :: token :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSafeTransferCallMem2 self o toWord value) (UInt256.ofNat 13) out σ k C)
    (houtNe : out.size ≠ 0) (hhi : 2 ^ 255 ≤ out.size)
    (houtSize : out.size < UInt256.size)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  exact RD.uniswapSafeTransferReturnNonemptyHugeReverts
    (base := (⟨292⟩ : UInt256)) (gasMarker := UInt256.ofNat 13)
    (R := token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
    h houtNe houtSize
    (skimSafeTransferCallMem2_mload64 self toWord value ho32 hoSize)
    (by decide)
    (by decide)
    (by
      rw [show (((⟨292⟩ : UInt256) + ⟨32⟩).toNat) = 324 from by decide]
      simpa [skimSafeTransferReturnDataActiveWords] using
        safeTransferReturnDataHugeCopyMemCost_gt_g g out hhi houtSize)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSafeTransferNonemptyFailureReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord token token1 ret sel : UInt256}
    {o out : ByteArray} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨0⟩ :: ⟨360⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token1 :: token :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSafeTransferCallMem2 self o toWord value) (UInt256.ofNat 13) out σ k C)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  obtain ⟨_, _, rd6652⟩ :=
    RD.uniswapSkimSafeTransferNonemptyReturnToCheck
      (self := self) (value := value) (toWord := toWord) (token := token)
      (token1 := token1) (ret := ret) (sel := sel) (status := (⟨0⟩ : UInt256))
      h houtNe houtSize ho32 hoSize
  exact RD.uniswapSafeTransferReturnNonemptyFailureReverts
    (R := token1 :: token :: toWord :: ⟨570⟩ :: sel :: []) rd6652
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSafeTransferFailureMessageFrom6697Reverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord token token1 ret sel status : UInt256}
    {o out : ByteArray} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6697⟩
      (⟨292⟩ :: status :: value :: toWord :: token :: ret :: token1 :: token :: toWord ::
        ⟨570⟩ :: sel :: [])
      (skimSafeTransferReturnDataMem self o toWord value out)
      (skimSafeTransferReturnDataActiveWords out) out σ k C)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  exact RD.uniswapSafeTransferReturnFailureMessageFrom6697Reverts
    (R := token1 :: token :: toWord :: ⟨570⟩ :: sel :: []) h (by simp)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSafeTransferNonemptyTrueStatusToLengthLoaded {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {self value toWord token token1 ret sel : UInt256}
    {o out : ByteArray} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨1⟩ :: ⟨360⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token1 :: token :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSafeTransferCallMem2 self o toWord value) (UInt256.ofNat 13) out σ k C)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6676⟩
      (UInt256.ofNat out.size :: ⟨324⟩ :: ⟨292⟩ :: ⟨1⟩ ::
        value :: toWord :: token :: ret :: token1 :: token :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSafeTransferReturnDataMem self o toWord value out)
      (skimSafeTransferReturnDataActiveWords out) out σ k' C' := by
  obtain ⟨_, _, rd6652⟩ :=
    RD.uniswapSkimSafeTransferNonemptyReturnToCheck
      (self := self) (value := value) (toWord := toWord) (token := token)
      (token1 := token1) (ret := ret) (sel := sel) (status := (⟨1⟩ : UInt256))
      h houtNe houtSize ho32 hoSize
  exact RD.uniswapSafeTransferReturnNonemptyTrueStatusToLengthLoaded
    (retPtr := (⟨324⟩ : UInt256)) (R := token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
    rd6652 houtNe houtSize
    (skimSafeTransferReturnDataMem_mload292 self toWord value out ho32 hoSize houtNe houtSize)
    (skimSafeTransferReturnDataActiveWords_mload292_same out houtSize)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSafeTransferNonemptyShortReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord token token1 ret sel : UInt256}
    {o out : ByteArray} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨1⟩ :: ⟨360⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token1 :: token :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSafeTransferCallMem2 self o toWord value) (UInt256.ofNat 13) out σ k C)
    (houtNe : out.size ≠ 0) (hshort : out.size < 32) (houtSize : out.size < 2 ^ 255)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  obtain ⟨_, _, rd6676⟩ :=
    RD.uniswapSkimSafeTransferNonemptyTrueStatusToLengthLoaded
      h houtNe houtSize ho32 hoSize
  exact RD.uniswapSafeTransferReturnNonemptyShortReverts rd6676 hshort houtSize
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSafeTransferNonemptyFalseReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord token token1 ret sel : UInt256}
    {o out : ByteArray} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨1⟩ :: ⟨360⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token1 :: token :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSafeTransferCallMem2 self o toWord value) (UInt256.ofNat 13) out σ k C)
    (houtNe : out.size ≠ 0) (hout32 : 32 ≤ out.size) (houtSize : out.size < 2 ^ 255)
    (hword :
      UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) = ⟨0⟩)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  obtain ⟨_, _, rd6676⟩ :=
    RD.uniswapSkimSafeTransferNonemptyTrueStatusToLengthLoaded
      h houtNe houtSize ho32 hoSize
  exact RD.uniswapSafeTransferReturnNonemptyFalseReverts
    (R := token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
    rd6676 hout32 houtSize hword
    (skimSafeTransferReturnDataMem_mload324 self toWord value out ho32 hoSize hout32
      houtSize)
    (skimSafeTransferReturnDataActiveWords_mload324_same out houtSize)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSafeTransferNonemptyTrueToRet {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord token token1 ret sel : UInt256}
    {o out : ByteArray} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨1⟩ :: ⟨360⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token1 :: token :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSafeTransferCallMem2 self o toWord value) (UInt256.ofNat 13) out σ k C)
    (houtNe : out.size ≠ 0) (hout32 : 32 ≤ out.size) (houtSize : out.size < 2 ^ 255)
    (hword :
      UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) ≠ ⟨0⟩)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret
      (token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferReturnDataMem self o toWord value out)
      (skimSafeTransferReturnDataActiveWords out) out σ k' C' := by
  obtain ⟨_, _, rd6676⟩ :=
    RD.uniswapSkimSafeTransferNonemptyTrueStatusToLengthLoaded
      h houtNe houtSize ho32 hoSize
  exact RD.uniswapSafeTransferReturnNonemptyTrueToRet
    (R := token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
    rd6676 hout32 houtSize hword
    (skimSafeTransferReturnDataMem_mload324 self toWord value out ho32 hoSize hout32
      houtSize)
    (skimSafeTransferReturnDataActiveWords_mload324_same out houtSize)
    hret
    (by simp only [List.length_cons, List.length_nil]; omega)

end UniswapV2Pair
