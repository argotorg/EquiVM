import Examples.Precompiles.Modexp.BaseTrivial

/-!
# Exact return block for bases zero and one
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option Elab.async false

def baseSmallReturnGas (I : ExecutionEnv) (baseValue modulusOffset modulusSize : Nat) : Nat :=
  68 + exponentZeroCopyGas modulusSize + isGt1Gas I modulusOffset modulusSize +
    if baseValue = 1 ∧
      1 < Model.bytesToNatPadded I.calldata modulusOffset modulusSize then 24 else 0

def wideBaseSmallTotalGas (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) : Nat :=
  79 + cdRangeGas I (wideExponentOffset baseSize)
      (wideModulusOffset baseSize exponentSize) +
    wideBaseSmallGas I baseSize +
    baseSmallReturnGas I (Model.bytesToNatPadded I.calldata 96 baseSize)
      (wideModulusOffset baseSize exponentSize) modulusSize

private theorem baseReturnPrefixDecodes :
    [decode runtimeBytecode ⟨196⟩, decode runtimeBytecode ⟨197⟩,
      decode runtimeBytecode ⟨198⟩, decode runtimeBytecode ⟨199⟩,
      decode runtimeBytecode ⟨201⟩, decode runtimeBytecode ⟨204⟩,
      decode runtimeBytecode ⟨205⟩, decode runtimeBytecode ⟨207⟩,
      decode runtimeBytecode ⟨208⟩, decode runtimeBytecode ⟨209⟩,
      decode runtimeBytecode ⟨210⟩, decode runtimeBytecode ⟨211⟩,
      decode runtimeBytecode ⟨212⟩, decode runtimeBytecode ⟨213⟩,
      decode runtimeBytecode ⟨216⟩] =
    [some (.DUP6, .none), some (.SWAP3, .none), some (.POP, .none),
      some (.Push .PUSH1, some (⟨1⟩, 1)),
      some (.Push .PUSH2, some (⟨217⟩, 2)), some (.DUP5, .none),
      some (.Push .PUSH1, some (⟨64⟩, 1)), some (.MLOAD, .none),
      some (.SWAP5, .none), some (.DUP2, .none), some (.CALLDATASIZE, .none),
      some (.DUP8, .none), some (.CALLDATACOPY, .none),
      some (.Push .PUSH2, some (⟨762⟩, 2)), some (.JUMP, .none)] := by
  native_decide

private theorem baseReturnSuffixDecodes :
    [decode runtimeBytecode ⟨217⟩, decode runtimeBytecode ⟨218⟩,
      decode runtimeBytecode ⟨219⟩, decode runtimeBytecode ⟨220⟩,
      decode runtimeBytecode ⟨221⟩, decode runtimeBytecode ⟨224⟩,
      decode runtimeBytecode ⟨225⟩, decode runtimeBytecode ⟨226⟩,
      decode runtimeBytecode ⟨227⟩, decode runtimeBytecode ⟨229⟩,
      decode runtimeBytecode ⟨230⟩, decode runtimeBytecode ⟨231⟩,
      decode runtimeBytecode ⟨232⟩, decode runtimeBytecode ⟨233⟩,
      decode runtimeBytecode ⟨234⟩, decode runtimeBytecode ⟨235⟩,
      decode runtimeBytecode ⟨236⟩] =
    [some (.JUMPDEST, .none), some (.SWAP2, .none), some (.EQ, .none),
      some (.AND, .none), some (.Push .PUSH2, some (⟨226⟩, 2)),
      some (.JUMPI, .none), some (.RETURN, .none), some (.JUMPDEST, .none),
      some (.Push .PUSH1, some (⟨1⟩, 1)), some (.PUSH0, .none),
      some (.NOT, .none), some (.DUP4, .none), some (.DUP4, .none),
      some (.ADD, .none), some (.ADD, .none), some (.MSTORE8, .none),
      some (.RETURN, .none)] := by
  native_decide

/-- Reserve the result buffer and evaluate the trusted modulus-greater-than-one predicate. -/
theorem reachBaseSmallPredicate {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseValue modulusOffset exponentSize exponentOffset baseSize modulusSize : Nat}
    {tail : List UInt256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hsize : modulusSize ≤ 1024) (hcalldata : I.calldata.size < 2 ^ 64)
    (hbound : modulusOffset + modulusSize + 32 < 2 ^ 64)
    (htail : tail.length ≤ 1006)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨196⟩
      (UInt256.ofNat baseValue :: UInt256.ofNat modulusOffset ::
        UInt256.ofNat exponentSize :: UInt256.ofNat exponentOffset ::
        UInt256.ofNat baseSize :: UInt256.ofNat modulusSize :: tail)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨217⟩
      (UInt256.ofNat
          (if 1 < Model.bytesToNatPadded I.calldata modulusOffset modulusSize then 1 else 0) ::
        (⟨1⟩ : UInt256) :: UInt256.ofNat baseValue :: (⟨128⟩ : UInt256) ::
        UInt256.ofNat modulusSize :: UInt256.ofNat exponentOffset ::
        UInt256.ofNat baseSize :: UInt256.ofNat modulusSize :: tail)
      solcFreePtrMem (exponentZeroActiveWords modulusSize) ByteArray.empty acc k'
      (C + 45 + exponentZeroCopyGas modulusSize +
        isGt1Gas I modulusOffset modulusSize) := by
  have hd := baseReturnPrefixDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10,
    hd11, hd12, hd13, hd14⟩
  have hsize256 : modulusSize < UInt256.size :=
    lt_trans (lt_of_le_of_lt hsize (by decide : 1024 < 2 ^ 64)) (by decide)
  have hcd256 : I.calldata.size < UInt256.size := lt_trans hcalldata (by decide)
  have rd207 := evm_run rd0 with [
    known dup6 hd0, known swap3 hd1, known pop hd2, known push1 hd3 ⟨1⟩,
    known push2 hd4 ⟨217⟩, known dup5 hd5, known push1 hd6 ⟨64⟩ ]
  have rd208 := RDx.mload 0 ⟨128⟩ (UInt256.ofNat 3) rd207 hd7
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', MachineState.M, haw, hstk]
      rw [show (UInt256.ofNat 3).toNat = 3 by native_decide,
        show (⟨64⟩ : UInt256).toNat = 64 by native_decide]
      native_decide)
    solcFreePtrMem_mload64 (by decide) (by simp only [List.length_cons]; omega)
  have rdCopy0 := evm_run rd208 with [
    known swap5 hd8, known dup2 hd9, known calldatasize hd10, known dup8 hd11 ]
  have rdCopy := RDx.calldatacopy
    (exponentZeroCopyMemoryGas modulusSize) solcFreePtrMem
    (exponentZeroActiveWords modulusSize) rdCopy0 hd12
    (by
      intro s haw hstk
      simp [exponentZeroCopyMemoryGas, exponentZeroActiveWords,
        exponentZeroWords, memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      rw [show (UInt256.ofNat 3).toNat = 3 by native_decide,
        show (⟨128⟩ : UInt256).toNat = 128 by native_decide,
        UInt256.toNat_ofNat_of_lt hsize256])
    (by
      rw [UInt256.toNat_ofNat_of_lt hcd256, UInt256.toNat_ofNat_of_lt hsize256]
      exact write_from_source_end_past_dest I.calldata solcFreePtrMem
        I.calldata.size 128 modulusSize (le_refl _)
          (by rw [solcFreePtrMem_size]; omega))
    (by
      simp [exponentZeroActiveWords, exponentZeroWords]
      rw [show (UInt256.ofNat 3).toNat = 3 by native_decide,
        show (⟨128⟩ : UInt256).toNat = 128 by native_decide,
        UInt256.toNat_ofNat_of_lt hsize256])
    (by simp only [List.length_cons]; omega)
  have rd762raw := evm_run rdCopy with [
    known push2 hd13 ⟨762⟩, known jump hd14 jumpDest_762 ]
  have rd762 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨762⟩
      (UInt256.ofNat modulusOffset :: UInt256.ofNat modulusSize :: (⟨217⟩ : UInt256) ::
        (⟨1⟩ : UInt256) :: UInt256.ofNat baseValue :: (⟨128⟩ : UInt256) ::
        UInt256.ofNat modulusSize :: UInt256.ofNat exponentOffset ::
        UInt256.ofNat baseSize :: UInt256.ofNat modulusSize :: tail)
      solcFreePtrMem (exponentZeroActiveWords modulusSize) ByteArray.empty acc
      (k + 15) (C + 45 + exponentZeroCopyGas modulusSize) := by
    exact rd762raw.withIndices (by omega) (by
      rw [UInt256.toNat_ofNat_of_lt hsize256]
      simp [exponentZeroCopyGas, GasConstants.Gverylow, GasConstants.Gcopy]
      omega)
  obtain ⟨k', rd217⟩ := isGt1ExactTrusted
    (tail := (⟨1⟩ : UInt256) :: UInt256.ofNat baseValue :: (⟨128⟩ : UInt256) ::
      UInt256.ofNat modulusSize :: UInt256.ofNat exponentOffset ::
      UInt256.ofNat baseSize :: UInt256.ofNat modulusSize :: tail)
    (by simp only [List.length_cons]; omega) hbound jumpDest_wide217 rd762
  exact ⟨k', rd217.withIndices rfl (by omega)⟩

private theorem baseOneStoreAddress {modulusSize : Nat} (hsize : modulusSize ≤ 1024) :
    (⟨128⟩ : UInt256) + UInt256.ofNat modulusSize + UInt256.lnot ⟨0⟩ =
      UInt256.ofNat (127 + modulusSize) := by
  apply u256_inj
  simp only [uadd_toNat]
  rw [UInt256.toNat_ofNat_of_lt (lt_trans (by omega : modulusSize < 2 ^ 64) (by decide)),
    show (⟨128⟩ : UInt256).toNat = 128 by native_decide,
    show (UInt256.lnot (⟨0⟩ : UInt256)).toNat = UInt256.size - 1 by
      unfold UInt256.lnot
      native_decide,
    UInt256.toNat_ofNat_of_lt
      (lt_trans (by omega : 127 + modulusSize < 2 ^ 64) (by decide))]
  have hs : 128 + modulusSize < UInt256.size := by
    exact lt_trans (by omega : 128 + modulusSize < 2 ^ 64) (by decide)
  rw [Nat.mod_eq_of_lt hs]
  have hminus : UInt256.size - 1 < UInt256.size := by
    exact Nat.sub_lt (by decide) (by decide)
  have hrewrite : 128 + modulusSize + (UInt256.size - 1) =
      (127 + modulusSize) + UInt256.size := by omega
  rw [hrewrite, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- Caller-visible return of the shared base-zero/base-one block. -/
theorem baseSmallReturnExact {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseValue modulusOffset exponentOffset baseSize modulusSize : Nat}
    {tail : List UInt256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hsize : modulusSize ≤ 1024) (hbase : baseValue ≤ 1) (htail : tail.length ≤ 1012)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨217⟩
      (UInt256.ofNat
          (if 1 < Model.bytesToNatPadded I.calldata modulusOffset modulusSize then 1 else 0) ::
        (⟨1⟩ : UInt256) :: UInt256.ofNat baseValue :: (⟨128⟩ : UInt256) ::
        UInt256.ofNat modulusSize :: UInt256.ofNat exponentOffset ::
        UInt256.ofNat baseSize :: UInt256.ofNat modulusSize :: tail)
      solcFreePtrMem (exponentZeroActiveWords modulusSize) ByteArray.empty acc k C) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I) acc
      (Model.natToBytes
        (if baseValue = 1 ∧
          1 < Model.bytesToNatPadded I.calldata modulusOffset modulusSize then 1 else 0)
        modulusSize)
      (C + 23 + if baseValue = 1 ∧
        1 < Model.bytesToNatPadded I.calldata modulusOffset modulusSize then 24 else 0) := by
  have hd := baseReturnSuffixDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10,
    hd11, hd12, hd13, hd14, hd15, hd16⟩
  have hsize256 : modulusSize < UInt256.size :=
    lt_trans (lt_of_le_of_lt hsize (by decide : 1024 < 2 ^ 64)) (by decide)
  have hwords256 := exponentZeroWords_lt_uint256 hsize
  interval_cases baseValue
  · have rd225 := evm_run rd0 with [
      known jumpdest hd0, known swap2 hd1, known eq hd2, known and hd3,
      known push2 hd4 ⟨226⟩, known jumpiNT hd5 (by
        split <;> native_decide) ]
    have hret := RDx.ret 0 (Model.natToBytes 0 modulusSize) rd225 hd6
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          exponentZeroActiveWords]
        rw [show (⟨128⟩ : UInt256).toNat = 128 by native_decide,
          UInt256.toNat_ofNat_of_lt hwords256,
          UInt256.toNat_ofNat_of_lt hsize256,
          exponentZeroWords_covers_return]
        omega)
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 by native_decide,
          UInt256.toNat_ofNat_of_lt hsize256,
          readWithPadding_past_end solcFreePtrMem 128 modulusSize
            (by rw [solcFreePtrMem_size]; omega) (by omega)]
        exact (model_natToBytes_zero_eq_zeroes modulusSize).symm)
      (by simp only [List.length_cons]; omega)
    simpa using hret
  · by_cases hgt : 1 < Model.bytesToNatPadded I.calldata modulusOffset modulusSize
    · have hpos : 0 < modulusSize := by
        by_contra hn
        have : modulusSize = 0 := Nat.eq_zero_of_not_pos hn
        subst modulusSize
        simp at hgt
      have rd226 := evm_run (rd0.withStack (by rw [if_pos hgt])) with [
        known jumpdest hd0, known swap2 hd1, known eq hd2, known and hd3,
        known push2 hd4 ⟨226⟩, known jumpiT hd5 (by native_decide) jumpDest_wide226 ]
      have rdStore0 := evm_run rd226 with [
        known jumpdest hd7, known push1 hd8 ⟨1⟩, known push0 hd9,
        known not hd10, known dup4 hd11, known dup4 hd12,
        known add hd13, known add hd14 ]
      rw [baseOneStoreAddress hsize] at rdStore0
      have rdStore := RDx.mstore8 0 (exponentOneMemory modulusSize)
        (exponentZeroActiveWords modulusSize) rdStore0 hd15
        (by
          intro s haw hstk
          simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
            exponentZeroActiveWords]
          rw [UInt256.toNat_ofNat_of_lt hwords256,
            UInt256.toNat_ofNat_of_lt
              (lt_trans (by omega : 127 + modulusSize < 2 ^ 64) (by decide)),
            exponentZeroWords_covers_last hpos]
          omega)
        (by
          rw [UInt256.toNat_ofNat_of_lt
            (lt_trans (by omega : 127 + modulusSize < 2 ^ 64) (by decide))]
          rw [show UInt8.ofNat (⟨1⟩ : UInt256).toNat = 1 by native_decide]
          rfl)
        (by
          simp [exponentZeroActiveWords]
          rw [UInt256.toNat_ofNat_of_lt hwords256,
            UInt256.toNat_ofNat_of_lt
              (lt_trans (by omega : 127 + modulusSize < 2 ^ 64) (by decide)),
            exponentZeroWords_covers_last hpos])
        (by simp only [List.length_cons]; omega)
      have hret := RDx.ret 0 (Model.natToBytes 1 modulusSize) rdStore hd16
        (by
          intro s haw hstk
          simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
            exponentZeroActiveWords]
          rw [show (⟨128⟩ : UInt256).toNat = 128 by native_decide,
            UInt256.toNat_ofNat_of_lt hwords256,
            UInt256.toNat_ofNat_of_lt hsize256,
            exponentZeroWords_covers_return]
          omega)
        (by
          rw [show (⟨128⟩ : UInt256).toNat = 128 by native_decide,
            UInt256.toNat_ofNat_of_lt hsize256]
          exact exponentOneMemory_read hsize hpos)
        (by simp only [List.length_cons]; omega)
      simpa [hgt] using hret
    · have rd225 := evm_run (rd0.withStack (by rw [if_neg hgt])) with [
        known jumpdest hd0, known swap2 hd1, known eq hd2, known and hd3,
        known push2 hd4 ⟨226⟩, known jumpiNT hd5 (by native_decide) ]
      have hret := RDx.ret 0 (Model.natToBytes 0 modulusSize) rd225 hd6
        (by
          intro s haw hstk
          simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
            exponentZeroActiveWords]
          rw [show (⟨128⟩ : UInt256).toNat = 128 by native_decide,
            UInt256.toNat_ofNat_of_lt hwords256,
            UInt256.toNat_ofNat_of_lt hsize256,
            exponentZeroWords_covers_return]
          omega)
        (by
          rw [show (⟨128⟩ : UInt256).toNat = 128 by native_decide,
            UInt256.toNat_ofNat_of_lt hsize256,
            readWithPadding_past_end solcFreePtrMem 128 modulusSize
              (by rw [solcFreePtrMem_size]; omega) (by omega)]
          exact (model_natToBytes_zero_eq_zeroes modulusSize).symm)
        (by simp only [List.length_cons]; omega)
      simpa [hgt] using hret

/-- Complete arbitrary-width base-zero/base-one path, stated using trusted `modPow`. -/
theorem wideBaseSmallExact {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize : Nat} {k C : Nat}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hsize : modulusSize ≤ 1024) (hcalldata : I.calldata.size < 2 ^ 64)
    (hbound : 96 + baseSize + exponentSize + modulusSize + 32 < 2 ^ 64)
    (hexp : Model.bytesToNatPadded I.calldata
      (wideExponentOffset baseSize) exponentSize ≠ 0)
    (hbase : Model.bytesToNatPadded I.calldata 96 baseSize ≤ 1)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨62⟩
      [UInt256.ofNat exponentSize, UInt256.ofNat baseSize, UInt256.ofNat modulusSize]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty acc k C) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I) acc
      (Model.natToBytes
        (Model.modPow
          (Model.bytesToNatPadded I.calldata 96 baseSize)
          (Model.bytesToNatPadded I.calldata (wideExponentOffset baseSize) exponentSize)
          (Model.bytesToNatPadded I.calldata
            (wideModulusOffset baseSize exponentSize) modulusSize))
        modulusSize)
      (C + wideBaseSmallTotalGas I baseSize exponentSize modulusSize) := by
  obtain ⟨k1, rd89⟩ := reachWideExponentNonzero (by omega) hexp rd0
  obtain ⟨k2, rd196⟩ := reachWideBaseSmall (by omega) hbase rd89
  obtain ⟨k3, rd217⟩ := reachBaseSmallPredicate
    (tail := []) hsize hcalldata (by unfold wideModulusOffset; omega) (by simp) rd196
  have hret := baseSmallReturnExact (tail := []) hsize hbase (by simp) rd217
  have hpure := model_modPow_base_le_one
    (Model.bytesToNatPadded I.calldata 96 baseSize)
    (Model.bytesToNatPadded I.calldata (wideExponentOffset baseSize) exponentSize)
    (Model.bytesToNatPadded I.calldata
      (wideModulusOffset baseSize exponentSize) modulusSize) hbase hexp
  rw [hpure]
  unfold wideBaseSmallTotalGas baseSmallReturnGas
  convert hret using 1 <;> omega

end Modexp
