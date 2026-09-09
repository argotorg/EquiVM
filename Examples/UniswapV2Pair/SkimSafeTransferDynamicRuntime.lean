import Examples.UniswapV2Pair.SkimSafeTransferReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## Dynamic `_safeTransfer` return-data tails -/

theorem skimSafeTransferReturnDataHugeCopyMemCost_gt_g (g : Sat256) (out : ByteArray)
    (hhi : 2 ^ 255 ≤ out.size) (hlo : out.size < UInt256.size) :
    g.toNat <
      Cₘ (UInt256.ofNat (MachineState.M (UInt256.ofNat 13).toNat 324 out.size)) -
        Cₘ (UInt256.ofNat 13) := by
  let M := MachineState.M (UInt256.ofNat 13).toNat 324 out.size
  have hMge : 2 ^ 250 ≤ M := by
    simp only [M]
    rw [show (UInt256.ofNat 13).toNat = 13 from by decide]
    unfold MachineState.M
    split
    · omega
    · apply le_trans ?_ (Nat.le_max_right _ _)
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      norm_num
      omega
  have hMlt : M < UInt256.size := by
    simp only [M]
    rw [show (UInt256.ofNat 13).toNat = 13 from by decide]
    unfold MachineState.M
    split
    · norm_num [UInt256.size]
    · apply max_lt
      · norm_num [UInt256.size]
      · rw [Nat.div_lt_iff_lt_mul (by norm_num)]
        norm_num [UInt256.size] at hlo ⊢
        omega
  have hdivLower : 2 ^ 491 ≤ M * M / 512 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have hMM : (2 ^ 250) * (2 ^ 250) ≤ M * M := Nat.mul_le_mul hMge hMge
    have hpow : (2 ^ 491) * 512 = (2 ^ 250) * (2 ^ 250) := by decide
    rwa [hpow]
  have hbig :
      UInt256.size + Cₘ (UInt256.ofNat 13) <
        Cₘ (UInt256.ofNat M) := by
    rw [show Cₘ (UInt256.ofNat 13) = 39 from by decide]
    rw [Cₘ, UInt256.toNat_ofNat_of_lt hMlt]
    simp only [GasConstants.Gmemory, Cₘ.QuadraticCeofficient]
    have hpow : UInt256.size + 39 < 2 ^ 491 := by decide
    omega
  have hg : g.toNat < UInt256.size := g.isLt
  have hcost :
      UInt256.size <
        Cₘ (UInt256.ofNat M) - Cₘ (UInt256.ofNat 13) := by
    omega
  simpa [M] using lt_trans hg hcost

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSafeTransferNonemptyHugeReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord token token1 ret sel status : UInt256}
    {o out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (status :: ⟨360⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token1 :: token :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSafeTransferCallMem2 self o toWord value) (UInt256.ofNat 13) out acc k C)
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
        skimSafeTransferReturnDataHugeCopyMemCost_gt_g g out hhi houtSize)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSafeTransferNonemptyFailureReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord token token1 ret sel : UInt256}
    {o out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨0⟩ :: ⟨360⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token1 :: token :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSafeTransferCallMem2 self o toWord value) (UInt256.ofNat 13) out acc k C)
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
    {o out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6697⟩
      (⟨292⟩ :: status :: value :: toWord :: token :: ret :: token1 :: token :: toWord ::
        ⟨570⟩ :: sel :: [])
      (skimSafeTransferReturnDataMem self o toWord value out)
      (skimSafeTransferReturnDataActiveWords out) out acc k C)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  exact RD.uniswapSafeTransferReturnFailureMessageFrom6697Reverts
    (R := token1 :: token :: toWord :: ⟨570⟩ :: sel :: []) h (by simp)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSafeTransferNonemptyTrueStatusToLengthLoaded {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {self value toWord token token1 ret sel : UInt256}
    {o out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨1⟩ :: ⟨360⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token1 :: token :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSafeTransferCallMem2 self o toWord value) (UInt256.ofNat 13) out acc k C)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6676⟩
      (UInt256.ofNat out.size :: ⟨324⟩ :: ⟨292⟩ :: ⟨1⟩ ::
        value :: toWord :: token :: ret :: token1 :: token :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSafeTransferReturnDataMem self o toWord value out)
      (skimSafeTransferReturnDataActiveWords out) out acc k' C' := by
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
    (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSafeTransferNonemptyShortReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord token token1 ret sel : UInt256}
    {o out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨1⟩ :: ⟨360⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token1 :: token :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSafeTransferCallMem2 self o toWord value) (UInt256.ofNat 13) out acc k C)
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
    {o out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨1⟩ :: ⟨360⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token1 :: token :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSafeTransferCallMem2 self o toWord value) (UInt256.ofNat 13) out acc k C)
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
    {o out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨1⟩ :: ⟨360⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token1 :: token :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSafeTransferCallMem2 self o toWord value) (UInt256.ofNat 13) out acc k C)
    (houtNe : out.size ≠ 0) (hout32 : 32 ≤ out.size) (houtSize : out.size < 2 ^ 255)
    (hword :
      UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) ≠ ⟨0⟩)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret
      (token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferReturnDataMem self o toWord value out)
      (skimSafeTransferReturnDataActiveWords out) out acc k' C' := by
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
