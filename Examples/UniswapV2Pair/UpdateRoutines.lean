import Examples.UniswapV2Pair.Routines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! # Shared `_update` runtime slices -/

abbrev uniswapUpdateTimestampWord (ee : ExecutionEnv) : UInt256 :=
  UInt256.land reserve32Mask (UInt256.ofNat ee.header.timestamp)

abbrev uniswapUpdateElapsedWord (slotWord : UInt256) (ee : ExecutionEnv) : UInt256 :=
  UInt256.sub (uniswapUpdateTimestampWord ee)
    (UInt256.land reserve32Mask (UInt256.div slotWord reserve224Shift))

abbrev uniswapUpdatePackedReserveWord
    (slotWord timestamp balance1 balance0 : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.mul (UInt256.land timestamp reserve32Mask) reserve224Shift)
    (UInt256.land (UInt256.sub reserve224Shift ⟨1⟩)
      (UInt256.lor
        (UInt256.mul reserve112Shift (UInt256.land reserve112Mask balance1))
        (UInt256.land (UInt256.lnot (UInt256.shiftLeft reserve112Mask ⟨112⟩))
          (UInt256.lor (UInt256.land reserve112Mask balance0)
            (UInt256.land (UInt256.lnot reserve112Mask) slotWord)))))

theorem uniswapUpdatePackedReserveWord_eq_setters
    (slotWord timestamp balance1 balance0 : UInt256) :
    setUint32Offset28Word
        (setUint112Offset14Word (setUint112Offset0Word slotWord balance0) balance1)
        timestamp =
      uniswapUpdatePackedReserveWord slotWord timestamp balance1 balance0 := by
  rfl

abbrev uniswapSyncTopic : UInt256 :=
  ⟨0x1c411e9a96e071241c2f21f7726b17ae89e3cab4c78be50e062b03a9fffbbad1⟩

abbrev uniswapSyncReserve0Word (packed : UInt256) : UInt256 :=
  UInt256.land reserve112Mask packed

abbrev uniswapSyncReserve1Word (packed : UInt256) : UInt256 :=
  UInt256.land reserve112Mask (UInt256.div packed reserve112Shift)

def uniswapUpdateOverflowStringWord : UInt256 :=
  UInt256.shiftLeft
    (⟨1905181576457202428093485646709101176076128087⟩ : UInt256) ⟨104⟩

noncomputable def uniswapSyncLogReserve0Mem (packed : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (uniswapSyncReserve0Word packed)).write 0 mem 128 32

noncomputable def uniswapSyncLogMem (packed : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (uniswapSyncReserve1Word packed)).write 0
    (uniswapSyncLogReserve0Mem packed mem) 160 32

set_option maxHeartbeats 1000000 in
theorem RD.uniswapUpdateOverflowStringRevertTail_aw6_size164 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {R : List UInt256} {mem : ByteArray}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6994⟩ R mem (UInt256.ofNat 6)
      rdata acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 5 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  have rd6998 := evm_run h with [
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rd7002 := rd6998.pushConst (⟨4594637⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd7021 := evm_run rd7002 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 0 (solcErrorStringMem0 mem) (UInt256.ofNat 6)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore 0 (solcErrorStringMem1 mem) (UInt256.ofNat 6)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨19⟩, push1 ⟨36⟩, dup3, add,
    raw mstore 3 (solcErrorStringMem2 (⟨19⟩ : UInt256) mem)
      (UInt256.ofNat 7) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov)]
  have rd7044 := rd7021.pushConst
    (⟨1905181576457202428093485646709101176076128087⟩ : UInt256)
    (width := 19) (op := .PUSH19) (by decide) (by decide) (by evm_ov)
  exact evm_run rd7044 with [
    push1 ⟨104⟩, shl, push1 ⟨68⟩, dup3, add,
    raw mstore 3
      (solcErrorStringMem3 (⟨19⟩ : UInt256) uniswapUpdateOverflowStringWord mem)
      (UInt256.ofNat 8) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide)
      mem_cost
      (solcErrorStringMem3_mload64_of_size164 (⟨19⟩ : UInt256)
        uniswapUpdateOverflowStringWord hmem hread64)
      (by decide) (by evm_ov),
    swap1, dup2, swap1, sub, push1 ⟨100⟩, add, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem RD.uniswapUpdateOverflowGuardFirstReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {reserve1 reserve0 balance1 balance0 : UInt256}
    {R : List UInt256} {mem : ByteArray} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6959⟩
      (reserve1 :: reserve0 :: balance1 :: balance0 :: R) mem (UInt256.ofNat 6) rdata acc
      k C)
    (hfail0 : UniswapV2Pair.reserve112Mask.toNat < balance0.toNat)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 9 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  have hgt0 : UInt256.gt balance0 UniswapV2Pair.reserve112Mask = ⟨1⟩ :=
    ugt_one hfail0
  have hgt0Lit :
      UInt256.gt balance0
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩) =
        ⟨1⟩ := by
    simpa [UniswapV2Pair.reserve112Mask] using hgt0
  have rd6973₀ := evm_run h with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨112⟩, shl, sub, dup5, gt,
    dup1, iszero, swap1, push2 ⟨6989⟩]
  have rd6973 := rd6973₀
  rw [hgt0Lit, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd6973
  have rd6989 := evm_run rd6973 with [jumpiT one_ne_zero_uint (by jump_dest)]
  have rd6994 := evm_run rd6989 with [
    jumpdest, push2 ⟨7060⟩, jumpiNT (by decide)]
  exact RD.uniswapUpdateOverflowStringRevertTail_aw6_size164 rd6994 hmem hread64
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapUpdateOverflowGuardSecondReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {reserve1 reserve0 balance1 balance0 : UInt256}
    {R : List UInt256} {mem : ByteArray} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6959⟩
      (reserve1 :: reserve0 :: balance1 :: balance0 :: R) mem (UInt256.ofNat 6) rdata acc
      k C)
    (hfit0 : balance0.toNat ≤ UniswapV2Pair.reserve112Mask.toNat)
    (hfail1 : UniswapV2Pair.reserve112Mask.toNat < balance1.toNat)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 9 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  have hgt0 : UInt256.gt balance0 UniswapV2Pair.reserve112Mask = ⟨0⟩ :=
    ugt_zero hfit0
  have hgt1 : UInt256.gt balance1 UniswapV2Pair.reserve112Mask = ⟨1⟩ :=
    ugt_one hfail1
  have hgt0Lit :
      UInt256.gt balance0
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩) =
        ⟨0⟩ := by
    simpa [UniswapV2Pair.reserve112Mask] using hgt0
  have hgt1Lit :
      UInt256.gt balance1
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩) =
        ⟨1⟩ := by
    simpa [UniswapV2Pair.reserve112Mask] using hgt1
  have rd6973₀ := evm_run h with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨112⟩, shl, sub, dup5, gt,
    dup1, iszero, swap1, push2 ⟨6989⟩]
  have rd6973 := rd6973₀
  rw [hgt0Lit] at rd6973
  have rd6977 := evm_run rd6973 with [jumpiNT (by decide)]
  have rd6978 := evm_run rd6977 with [pop]
  have rd6989₀ := evm_run rd6978 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨112⟩, shl, sub, dup4, gt, iszero,
    jumpdest, push2 ⟨7060⟩]
  have rd6989 := rd6989₀
  rw [hgt1Lit, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd6989
  have rd6994 := evm_run rd6989 with [jumpiNT (by decide)]
  exact RD.uniswapUpdateOverflowStringRevertTail_aw6_size164 rd6994 hmem hread64
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
/-- Shared `_update` success guard: both balances fit in the packed `uint112` reserve fields,
so control jumps past the `UniswapV2: OVERFLOW` revert block. -/
theorem RD.uniswapUpdateOverflowGuardOk {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {reserve1 reserve0 balance1 balance0 : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6959⟩
      (reserve1 :: reserve0 :: balance1 :: balance0 :: R) mem aw rdata acc k C)
    (hfit0 : balance0.toNat ≤ UniswapV2Pair.reserve112Mask.toNat)
    (hfit1 : balance1.toNat ≤ UniswapV2Pair.reserve112Mask.toNat)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7060⟩
      (reserve1 :: reserve0 :: balance1 :: balance0 :: R) mem aw rdata acc k' C' := by
  have hgt0 : UInt256.gt balance0 UniswapV2Pair.reserve112Mask = ⟨0⟩ :=
    ugt_zero hfit0
  have hgt1 : UInt256.gt balance1 UniswapV2Pair.reserve112Mask = ⟨0⟩ :=
    ugt_zero hfit1
  have hgt0Lit :
      UInt256.gt balance0
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩) =
        ⟨0⟩ := by
    simpa [UniswapV2Pair.reserve112Mask] using hgt0
  have hgt1Lit :
      UInt256.gt balance1
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩) =
        ⟨0⟩ := by
    simpa [UniswapV2Pair.reserve112Mask] using hgt1
  have rd6973₀ := evm_run h with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨112⟩, shl, sub, dup5, gt,
    dup1, iszero, swap1, push2 ⟨6989⟩]
  have rd6973 := rd6973₀
  rw [hgt0Lit] at rd6973
  have rd6977 := evm_run rd6973 with [jumpiNT (by decide)]
  have rd6978 := evm_run rd6977 with [pop]
  have rd6989₀ := evm_run rd6978 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨112⟩, shl, sub, dup4, gt, iszero,
    jumpdest, push2 ⟨7060⟩]
  have rd6989 := rd6989₀
  rw [hgt1Lit, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd6989
  exact ⟨_, _, evm_run rd6989 with [jumpiT one_ne_zero_uint (by jump_dest)]⟩

set_option maxHeartbeats 1000000 in
/-- Shared `_update` slice for the `timeElapsed == 0` path. It computes the packed-slot
timestamp delta and jumps to the reserve-write block, skipping cumulative price updates. -/
theorem RD.uniswapUpdateElapsedZeroSkipsCumulatives {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {reserve1 reserve0 balance1 balance0 : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7060⟩
      (reserve1 :: reserve0 :: balance1 :: balance0 :: R) mem aw rdata acc k C)
    (helapsed0 :
      UInt256.land
        (UInt256.sub (UInt256.land reserve32Mask (UInt256.ofNat ee.header.timestamp))
          (UInt256.land reserve32Mask
            (UInt256.div
              (acc.2.find? ee.codeOwner |>.option ⟨0⟩
                (fun ac => ac.storage.findD ⟨8⟩ ⟨0⟩))
              reserve224Shift)))
        reserve32Mask = ⟨0⟩)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7241⟩
      (UInt256.sub (UInt256.land reserve32Mask (UInt256.ofNat ee.header.timestamp))
          (UInt256.land reserve32Mask
            (UInt256.div
              (acc.2.find? ee.codeOwner |>.option ⟨0⟩
                (fun ac => ac.storage.findD ⟨8⟩ ⟨0⟩))
              reserve224Shift)) ::
        UInt256.land reserve32Mask (UInt256.ofNat ee.header.timestamp) ::
        reserve1 :: reserve0 :: balance1 :: balance0 :: R)
      mem aw rdata acc k' C' := by
  have rd7063 := evm_run h with [jumpdest, push1 ⟨8⟩]
  obtain ⟨_, _, rd7064⟩ := rd7063.sload (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd7069 := evm_run rd7064 with [push4 ⟨4294967295⟩]
  have rd7070 := RD.timestamp rd7069 (by native_decide) (by evm_ov)
  have rd7091₀ := evm_run rd7070 with [
    dup2, and, swap2, push1 ⟨1⟩, push1 ⟨224⟩, shl, swap1, div, dup2, and,
    dup3, sub, swap1, dup2, and, iszero, dup1, iszero, swap1, push2 ⟨7108⟩]
  have rd7091 := rd7091₀
  rw [helapsed0, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide,
    show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd7091
  have rd7108 := evm_run rd7091 with [jumpiT one_ne_zero_uint (by jump_dest)]
  have rd7111 := evm_run rd7108 with [jumpdest, dup1, iszero, push2 ⟨7128⟩]
  have rd7128 := evm_run rd7111 with [jumpiT one_ne_zero_uint (by jump_dest)]
  have rd7130 := evm_run rd7128 with [jumpdest, iszero, push2 ⟨7241⟩]
  exact ⟨_, _, evm_run rd7130 with [jumpiT one_ne_zero_uint (by jump_dest)]⟩

set_option maxHeartbeats 1000000 in
/-- Shared `_update` slice for the condition-false branch where `timeElapsed != 0` but the
previous packed `reserve0` is zero. The cumulative price updates are skipped. -/
theorem RD.uniswapUpdateReserve0ZeroSkipsCumulatives {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {reserve1 reserve0 balance1 balance0 : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7060⟩
      (reserve1 :: reserve0 :: balance1 :: balance0 :: R) mem aw rdata acc k C)
    (helapsedNe :
      UInt256.land
        (UInt256.sub (UInt256.land reserve32Mask (UInt256.ofNat ee.header.timestamp))
          (UInt256.land reserve32Mask
            (UInt256.div
              (acc.2.find? ee.codeOwner |>.option ⟨0⟩
                (fun ac => ac.storage.findD ⟨8⟩ ⟨0⟩))
              reserve224Shift)))
        reserve32Mask ≠ ⟨0⟩)
    (hreserve0Zero : UInt256.land reserve0 reserve112Mask = ⟨0⟩)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7241⟩
      (UInt256.sub (UInt256.land reserve32Mask (UInt256.ofNat ee.header.timestamp))
          (UInt256.land reserve32Mask
            (UInt256.div
              (acc.2.find? ee.codeOwner |>.option ⟨0⟩
                (fun ac => ac.storage.findD ⟨8⟩ ⟨0⟩))
              reserve224Shift)) ::
        UInt256.land reserve32Mask (UInt256.ofNat ee.header.timestamp) ::
        reserve1 :: reserve0 :: balance1 :: balance0 :: R)
      mem aw rdata acc k' C' := by
  have helapsedIsZero :
      UInt256.isZero
        (UInt256.land
          (UInt256.sub (UInt256.land reserve32Mask (UInt256.ofNat ee.header.timestamp))
            (UInt256.land reserve32Mask
              (UInt256.div
                (acc.2.find? ee.codeOwner |>.option ⟨0⟩
                  (fun ac => ac.storage.findD ⟨8⟩ ⟨0⟩))
                reserve224Shift)))
          reserve32Mask) = ⟨0⟩ :=
    isZero_eq_zero_of_ne helapsedNe
  have hreserve0ZeroLit :
      UInt256.land reserve0
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩) =
        ⟨0⟩ := by
    simpa [reserve112Mask, reserve112Shift] using hreserve0Zero
  have rd7063 := evm_run h with [jumpdest, push1 ⟨8⟩]
  obtain ⟨_, _, rd7064⟩ := rd7063.sload (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd7069 := evm_run rd7064 with [push4 ⟨4294967295⟩]
  have rd7070 := RD.timestamp rd7069 (by native_decide) (by evm_ov)
  have rd7091₀ := evm_run rd7070 with [
    dup2, and, swap2, push1 ⟨1⟩, push1 ⟨224⟩, shl, swap1, div, dup2, and,
    dup3, sub, swap1, dup2, and, iszero, dup1, iszero, swap1, push2 ⟨7108⟩]
  have rd7091 := rd7091₀
  rw [helapsedIsZero, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd7091
  have rd7095 := evm_run rd7091 with [jumpiNT (by decide)]
  have rd7108₀ := evm_run rd7095 with [
    pop, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨112⟩, shl, sub, dup5, and, iszero,
    iszero]
  have rd7108 := rd7108₀
  rw [hreserve0ZeroLit, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide,
    show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd7108
  have rd7111 := evm_run rd7108 with [jumpdest, dup1, iszero, push2 ⟨7128⟩]
  have rd7128 := evm_run rd7111 with [jumpiT one_ne_zero_uint (by jump_dest)]
  have rd7130 := evm_run rd7128 with [jumpdest, iszero, push2 ⟨7241⟩]
  exact ⟨_, _, evm_run rd7130 with [jumpiT one_ne_zero_uint (by jump_dest)]⟩

set_option maxHeartbeats 1000000 in
/-- Shared `_update` slice for the condition-false branch where `timeElapsed != 0`, `reserve0`
is nonzero, and the previous packed `reserve1` is zero. The cumulative price updates are skipped. -/
theorem RD.uniswapUpdateReserve1ZeroSkipsCumulatives {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {reserve1 reserve0 balance1 balance0 : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7060⟩
      (reserve1 :: reserve0 :: balance1 :: balance0 :: R) mem aw rdata acc k C)
    (helapsedNe :
      UInt256.land
        (UInt256.sub (UInt256.land reserve32Mask (UInt256.ofNat ee.header.timestamp))
          (UInt256.land reserve32Mask
            (UInt256.div
              (acc.2.find? ee.codeOwner |>.option ⟨0⟩
                (fun ac => ac.storage.findD ⟨8⟩ ⟨0⟩))
              reserve224Shift)))
        reserve32Mask ≠ ⟨0⟩)
    (hreserve0Ne : UInt256.land reserve0 reserve112Mask ≠ ⟨0⟩)
    (hreserve1Zero : UInt256.land reserve1 reserve112Mask = ⟨0⟩)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7241⟩
      (UInt256.sub (UInt256.land reserve32Mask (UInt256.ofNat ee.header.timestamp))
          (UInt256.land reserve32Mask
            (UInt256.div
              (acc.2.find? ee.codeOwner |>.option ⟨0⟩
                (fun ac => ac.storage.findD ⟨8⟩ ⟨0⟩))
              reserve224Shift)) ::
        UInt256.land reserve32Mask (UInt256.ofNat ee.header.timestamp) ::
        reserve1 :: reserve0 :: balance1 :: balance0 :: R)
      mem aw rdata acc k' C' := by
  have helapsedIsZero :
      UInt256.isZero
        (UInt256.land
          (UInt256.sub (UInt256.land reserve32Mask (UInt256.ofNat ee.header.timestamp))
            (UInt256.land reserve32Mask
              (UInt256.div
                (acc.2.find? ee.codeOwner |>.option ⟨0⟩
                  (fun ac => ac.storage.findD ⟨8⟩ ⟨0⟩))
                reserve224Shift)))
          reserve32Mask) = ⟨0⟩ :=
    isZero_eq_zero_of_ne helapsedNe
  have hreserve0NeLit :
      UInt256.land reserve0
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩) ≠
        ⟨0⟩ := by
    simpa [reserve112Mask, reserve112Shift] using hreserve0Ne
  have hreserve0IsZero :
      UInt256.isZero
        (UInt256.land reserve0
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)) =
        ⟨0⟩ :=
    isZero_eq_zero_of_ne hreserve0NeLit
  have hreserve1ZeroLit :
      UInt256.land reserve1
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩) =
        ⟨0⟩ := by
    simpa [reserve112Mask, reserve112Shift] using hreserve1Zero
  have rd7063 := evm_run h with [jumpdest, push1 ⟨8⟩]
  obtain ⟨_, _, rd7064⟩ := rd7063.sload (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd7069 := evm_run rd7064 with [push4 ⟨4294967295⟩]
  have rd7070 := RD.timestamp rd7069 (by native_decide) (by evm_ov)
  have rd7091₀ := evm_run rd7070 with [
    dup2, and, swap2, push1 ⟨1⟩, push1 ⟨224⟩, shl, swap1, div, dup2, and,
    dup3, sub, swap1, dup2, and, iszero, dup1, iszero, swap1, push2 ⟨7108⟩]
  have rd7091 := rd7091₀
  rw [helapsedIsZero, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd7091
  have rd7095 := evm_run rd7091 with [jumpiNT (by decide)]
  have rd7108₀ := evm_run rd7095 with [
    pop, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨112⟩, shl, sub, dup5, and, iszero,
    iszero]
  have rd7108 := rd7108₀
  rw [hreserve0IsZero, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd7108
  have rd7111 := evm_run rd7108 with [jumpdest, dup1, iszero, push2 ⟨7128⟩]
  have rd7115 := evm_run rd7111 with [jumpiNT (by decide)]
  have rd7128₀ := evm_run rd7115 with [
    pop, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨112⟩, shl, sub, dup4, and, iszero,
    iszero]
  have rd7128 := rd7128₀
  rw [hreserve1ZeroLit, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide,
    show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd7128
  have rd7130 := evm_run rd7128 with [jumpdest, iszero, push2 ⟨7241⟩]
  exact ⟨_, _, evm_run rd7130 with [jumpiT one_ne_zero_uint (by jump_dest)]⟩

set_option maxHeartbeats 1000000 in
/-- Shared `_update` reserve write. Starting at the common reserve-write block, it packs
`balance0`, `balance1`, and the 32-bit timestamp into slot 8 and stores it. -/
theorem RD.uniswapUpdateStorePackedReserves {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ}
    {elapsed timestamp reserve1 reserve0 balance1 balance0 : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7241⟩
      (elapsed :: timestamp :: reserve1 :: reserve0 :: balance1 :: balance0 :: R)
      mem aw rdata acc k C)
    (hperm : ee.perm = true)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7339⟩
      (reserve112Shift :: reserve112Mask ::
        uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ acc.2 ee) timestamp balance1
          balance0 ::
        elapsed :: timestamp :: reserve1 :: reserve0 :: balance1 :: balance0 :: R)
      mem aw rdata
      (acc.1, sstoreAccountMap ee.codeOwner acc.2 ⟨8⟩
        (uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ acc.2 ee) timestamp balance1
          balance0))
      k' C' := by
  have rd7244 := evm_run h with [jumpdest, push1 ⟨8⟩, dup1]
  obtain ⟨_, _, rd7246⟩ := rd7244.sload (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd7261 := rd7246.pushConst reserve112Mask (width := 14) (op := .PUSH14)
    (by decide) (by decide) (by evm_ov)
  have rd7278 := evm_run rd7261 with [
    not, and, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨112⟩, shl, sub, dup9, dup2, and,
    swap2, swap1, swap2, lor]
  have rd7293 := rd7278.pushConst reserve112Mask (width := 14) (op := .PUSH14)
    (by decide) (by decide) (by evm_ov)
  have rd7338 := evm_run rd7293 with [
    push1 ⟨112⟩, shl, not, and,
    push1 ⟨1⟩, push1 ⟨112⟩, shl, dup9, dup4, and, dup2, mul,
    swap2, swap1, swap2, lor,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨224⟩, shl, sub, and,
    push1 ⟨1⟩, push1 ⟨224⟩, shl, push4 ⟨4294967295⟩, dup8, and, mul,
    lor, swap3, dup4, swap1]
  obtain ⟨_, _, rd7339⟩ := rd7338.sstore hperm (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by
    simpa [uniswapUpdatePackedReserveWord, uniswapSlotWord, reserve112Shift, reserve112Mask,
      reserve224Shift, reserve32Mask] using rd7339⟩

set_option maxHeartbeats 3000000 in
/-- Shared `_update` suffix that emits the `Sync(uint112,uint112)` event from the packed reserve
word and jumps to the dynamic return pc. The memory-cost hypotheses keep the helper independent of
the caller's current memory-active-word shape. -/
theorem RD.uniswapUpdateEmitSyncAndJump {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ}
    {packed elapsed timestamp reserve1 reserve0 balance1 balance0 ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw awLoad awLog : UInt256}
    {mcostLoad mcostStore0 mcostStore1 mcostLoadLog mcostLog : ℕ}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7339⟩
      (reserve112Shift :: reserve112Mask :: packed :: elapsed :: timestamp :: reserve1 ::
        reserve0 :: balance1 :: balance0 :: ret :: R)
      mem aw rdata acc k C)
    (hmcLoad : ∀ s : State, s.machineState.activeWords = aw →
      s.machineState.stack = ⟨64⟩ :: ⟨64⟩ :: reserve112Shift :: reserve112Mask :: packed ::
        elapsed :: timestamp :: reserve1 :: reserve0 :: balance1 :: balance0 :: ret :: R →
      memoryExpansionCost s .MLOAD = mcostLoad)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩)
    (hawLoad : UInt256.ofNat (MachineState.M aw.toNat 64 32) = awLoad)
    (hmcStore0 : ∀ s : State, s.machineState.activeWords = awLoad →
      s.machineState.stack = ⟨128⟩ :: uniswapSyncReserve0Word packed :: ⟨128⟩ ::
        ⟨64⟩ :: reserve112Shift :: reserve112Mask :: packed :: elapsed :: timestamp ::
        reserve1 :: reserve0 :: balance1 :: balance0 :: ret :: R →
      memoryExpansionCost s .MSTORE = mcostStore0)
    (hawStore0 : UInt256.ofNat (MachineState.M awLoad.toNat 128 32) = awLog)
    (hmcStore1 : ∀ s : State, s.machineState.activeWords = awLog →
      s.machineState.stack = ((⟨128⟩ : UInt256) + ⟨32⟩) ::
        uniswapSyncReserve1Word packed :: ⟨128⟩ :: ⟨64⟩ :: elapsed :: timestamp ::
        reserve1 :: reserve0 :: balance1 :: balance0 :: ret :: R →
      memoryExpansionCost s .MSTORE = mcostStore1)
    (hawStore1 :
      UInt256.ofNat (MachineState.M awLog.toNat (((⟨128⟩ : UInt256) + ⟨32⟩).toNat) 32) =
        awLog)
    (hmcLoadLog : ∀ s : State, s.machineState.activeWords = awLog →
      s.machineState.stack = ⟨64⟩ :: ⟨128⟩ :: ⟨64⟩ :: elapsed :: timestamp ::
        reserve1 :: reserve0 :: balance1 :: balance0 :: ret :: R →
      memoryExpansionCost s .MLOAD = mcostLoadLog)
    (hmload64Log :
      (if (⟨64⟩ : UInt256).toNat ≥ (uniswapSyncLogMem packed mem).size
          ∨ (⟨64⟩ : UInt256) ≥ awLog * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((uniswapSyncLogMem packed mem).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hawLoadLog : UInt256.ofNat (MachineState.M awLog.toNat 64 32) = awLog)
    (hmcLog : ∀ s : State, s.machineState.activeWords = awLog →
      s.machineState.stack = ⟨128⟩ ::
        ((⟨64⟩ : UInt256) + UInt256.sub ⟨128⟩ ⟨128⟩) :: uniswapSyncTopic ::
        elapsed :: timestamp :: reserve1 :: reserve0 :: balance1 :: balance0 :: ret :: R →
      memoryExpansionCost s .LOG1 = mcostLog)
    (hawLog : UInt256.ofNat
      (MachineState.M awLog.toNat 128
        (((⟨64⟩ : UInt256) + UInt256.sub ⟨128⟩ ⟨128⟩).toNat)) =
        awLog)
    (hperm : ee.perm = true)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret R
      (uniswapSyncLogMem packed mem) awLog rdata acc k' C' := by
  have rd7342 := evm_run h with [
    push1 ⟨64⟩, dup1,
    raw mload mcostLoad ⟨128⟩ awLoad (by decide) hmcLoad hmload64 hawLoad (by evm_ov)]
  have rd7347₀ := evm_run rd7342 with [dup5, dup5, and, dup2]
  have rd7348 := rd7347₀.mstore mcostStore0 (uniswapSyncLogReserve0Mem packed mem) awLog
    (by decide) hmcStore0 (by rfl) hawStore0 (by evm_ov)
  have rd7359₀ := evm_run rd7348 with [
    swap2, swap1, swap4, div, swap1, swap2, and, push1 ⟨32⟩, dup3, add]
  have rd7360 := rd7359₀.mstore mcostStore1 (uniswapSyncLogMem packed mem) awLog
    (by decide) hmcStore1
    (by
      rw [show (((⟨128⟩ : UInt256) + ⟨32⟩).toNat) = 160 from by decide]
      rfl)
    hawStore1 (by evm_ov)
  have rd7362 := evm_run rd7360 with [
    dup2,
    raw mload mcostLoadLog ⟨128⟩ awLog (by decide) hmcLoadLog hmload64Log hawLoadLog
      (by evm_ov)]
  have rd7395 := rd7362.pushConst uniswapSyncTopic (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd7404 := evm_run rd7395 with [
    swap3, swap2, dup2, swap1, sub, swap1, swap2, add, swap1]
  have rd7405 := rd7404.log1 mcostLog awLog (by decide) hperm hmcLog hawLog
    (by simp only [List.length_cons]; omega)
  have rd7411 := evm_run rd7405 with [pop, pop, pop, pop, pop, pop]
  exact ⟨_, _, rd7411.jump (by decide) hret (by evm_ov)⟩

end UniswapV2Pair
