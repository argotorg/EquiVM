import Examples.UniswapV2Pair.SkimSafeTransferReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

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
  obtain ⟨k6652, C6652, rd6652⟩ :=
    RD.uniswapSkimSafeTransferNonemptyReturnToCheck
      (self := self) (value := value) (toWord := toWord) (token := token)
      (token1 := token1) (ret := ret) (sel := sel) (status := (⟨1⟩ : UInt256))
      h houtNe houtSize ho32 hoSize
  have hsizeNe : UInt256.ofNat out.size ≠ ⟨0⟩ := by
    intro hzero
    have hnat : (UInt256.ofNat out.size).toNat = 0 := by
      rw [hzero]
      rfl
    rw [UInt256.toNat_ofNat_of_lt (lt_size_of_lt_sign houtSize)] at hnat
    exact houtNe hnat
  have hsizeIsZero : UInt256.isZero (UInt256.ofNat out.size) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hsizeNe
  have hload292 :=
    skimSafeTransferReturnDataMem_mload292 self toWord value out ho32 hoSize houtNe
      houtSize
  have haw292 := skimSafeTransferReturnDataActiveWords_mload292_same out houtSize
  have rd6661 := evm_run rd6652 with [
    dup2, dup1, iszero, push2 ⟨6692⟩, jumpiNT (by native_decide), pop, dup1]
  have rd6662 := RD.mload
    0 (UInt256.ofNat out.size) (skimSafeTransferReturnDataActiveWords out)
    rd6661 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, haw292])
    hload292 haw292
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6675 := evm_run rd6662 with [
    iszero, dup1, push2 ⟨6692⟩, jumpiNT hsizeIsZero, pop, dup1, dup1,
    push1 ⟨32⟩, add, swap1]
  have rd6676 := RD.mload
    0 (UInt256.ofNat out.size) (skimSafeTransferReturnDataActiveWords out)
    rd6675 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, haw292])
    hload292 haw292
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by
    simpa [show (⟨32⟩ : UInt256) + ⟨292⟩ = ⟨324⟩ by native_decide] using rd6676⟩

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
  obtain ⟨k6676, C6676, rd6676⟩ :=
    RD.uniswapSkimSafeTransferNonemptyTrueStatusToLengthLoaded
      h houtNe houtSize ho32 hoSize
  have rd6684₀ := evm_run rd6676 with [push1 ⟨32⟩, dup2, lt, iszero, push2 ⟨6689⟩]
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨32⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      UInt256.toNat_ofNat_of_lt (lt_size_of_lt_sign houtSize)]
    exact hshort
  have rd6684 := rd6684₀
  rw [hlt, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd6684
  have rd6685 := evm_run rd6684 with [jumpiNT (by native_decide)]
  exact RD.uniswapPush1Dup1Revert0 rd6685 (by native_decide)
    (by native_decide) (by native_decide)
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
  obtain ⟨k6676, C6676, rd6676⟩ :=
    RD.uniswapSkimSafeTransferNonemptyTrueStatusToLengthLoaded
      h houtNe houtSize ho32 hoSize
  have rd6684₀ := evm_run rd6676 with [push1 ⟨32⟩, dup2, lt, iszero, push2 ⟨6689⟩]
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨32⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      UInt256.toNat_ofNat_of_lt (lt_size_of_lt_sign houtSize)]
    exact hout32
  have rd6684 := rd6684₀
  rw [hlt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd6684
  have rd6691 := evm_run rd6684 with [jumpiT (by native_decide) (by jump_dest), jumpdest, pop]
  have haw324 := skimSafeTransferReturnDataActiveWords_mload324_same out houtSize
  have rd6692₀ := RD.mload
    0 (UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)))
    (skimSafeTransferReturnDataActiveWords out) rd6691 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, haw324])
    (skimSafeTransferReturnDataMem_mload324 self toWord value out ho32 hoSize hout32
      houtSize)
    haw324
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6692 := rd6692₀
  rw [hword] at rd6692
  have rd6697 := evm_run rd6692 with [
    jumpdest, push2 ⟨6773⟩, jumpiNT (by native_decide)]
  obtain ⟨k6697, C6697, rd6697'⟩ : ∃ k' C',
      RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6697⟩
        (⟨292⟩ :: ⟨1⟩ :: value :: toWord :: token :: ret :: token1 :: token ::
          toWord :: ⟨570⟩ :: sel :: [])
        (skimSafeTransferReturnDataMem self o toWord value out)
        (skimSafeTransferReturnDataActiveWords out) out acc k' C' := by
    exact ⟨_, _, by simpa using rd6697⟩
  exact RD.uniswapSkimSafeTransferFailureMessageFrom6697Reverts
    rd6697' houtNe houtSize ho32 hoSize

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
  obtain ⟨k6676, C6676, rd6676⟩ :=
    RD.uniswapSkimSafeTransferNonemptyTrueStatusToLengthLoaded
      h houtNe houtSize ho32 hoSize
  have rd6684₀ := evm_run rd6676 with [push1 ⟨32⟩, dup2, lt, iszero, push2 ⟨6689⟩]
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨32⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      UInt256.toNat_ofNat_of_lt (lt_size_of_lt_sign houtSize)]
    exact hout32
  have rd6684 := rd6684₀
  rw [hlt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd6684
  have rd6691 := evm_run rd6684 with [jumpiT (by native_decide) (by jump_dest), jumpdest, pop]
  have haw324 := skimSafeTransferReturnDataActiveWords_mload324_same out houtSize
  have rd6692₀ := RD.mload
    0 (UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)))
    (skimSafeTransferReturnDataActiveWords out) rd6691 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, haw324])
    (skimSafeTransferReturnDataMem_mload324 self toWord value out ho32 hoSize hout32
      houtSize)
    haw324
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6692 := rd6692₀
  have rd6773 := evm_run rd6692 with [
    jumpdest, push2 ⟨6773⟩, jumpiT hword (by jump_dest)]
  exact ⟨_, _, evm_run rd6773 with [jumpdest, pop, pop, pop, pop, pop,
    jump hret]⟩

end UniswapV2Pair
