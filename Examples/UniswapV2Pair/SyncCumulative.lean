import Examples.UniswapV2Pair.Sync

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## Exact cumulative-update source state for `sync()` -/

abbrev reserve224Mask : UInt256 :=
  UInt256.sub reserve224Shift ⟨1⟩

abbrev uniswapUpdateEncodedUQ112 (w : UInt256) : UInt256 :=
  UInt256.mul reserve112Shift (UInt256.land reserve112Mask w)

abbrev uniswapUpdateUQ112Price (numerator denominator : UInt256) : UInt256 :=
  UInt256.div
    (UInt256.land (UInt256.land reserve224Mask (uniswapUpdateEncodedUQ112 numerator))
      reserve224Mask)
    (UInt256.land denominator reserve112Mask)

abbrev uniswapUpdateElapsedFromStorage (σ : AccountMap) (ee : ExecutionEnv) : UInt256 :=
  UInt256.sub (UInt256.land reserve32Mask (UInt256.ofNat ee.header.timestamp))
    (UInt256.land reserve32Mask
      (UInt256.div
        (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨8⟩ ⟨0⟩))
        reserve224Shift))

abbrev uniswapUpdatePrice0CumulativeWord
    (σ : AccountMap) (ee : ExecutionEnv)
    (elapsed reserve1 reserve0 : UInt256) : UInt256 :=
  UInt256.mul (UInt256.land reserve224Mask (uniswapUpdateUQ112Price reserve1 reserve0))
    (UInt256.land reserve32Mask elapsed) + uniswapSlotWord ⟨9⟩ σ ee

abbrev uniswapUpdatePrice1CumulativeWord
    (σ : AccountMap) (ee : ExecutionEnv)
    (elapsed reserve0 reserve1 : UInt256) : UInt256 :=
  UInt256.mul (UInt256.land reserve224Mask (uniswapUpdateUQ112Price reserve0 reserve1))
    (UInt256.land elapsed reserve32Mask) + uniswapSlotWord ⟨10⟩ σ ee

abbrev uniswapUpdateReserve0Word (σ : AccountMap) (ee : ExecutionEnv) : UInt256 :=
  UInt256.land (uniswapSlotWord ⟨8⟩ σ ee) reserve112Mask

abbrev uniswapUpdateReserve1Word (σ : AccountMap) (ee : ExecutionEnv) : UInt256 :=
  UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σ ee) reserve112Shift) reserve112Mask

abbrev uniswapUpdatePrice0CumulativeMap (σ : AccountMap) (ee : ExecutionEnv) :
    AccountMap :=
  let elapsed := uniswapUpdateElapsedFromStorage σ ee
  let reserve0 := uniswapUpdateReserve0Word σ ee
  let reserve1 := uniswapUpdateReserve1Word σ ee
  let price0 := uniswapUpdatePrice0CumulativeWord σ ee elapsed reserve1 reserve0
  sstoreAccountMap ee.codeOwner σ ⟨9⟩ price0

abbrev uniswapUpdatePrice1CumulativeMap (σ : AccountMap) (ee : ExecutionEnv) :
    AccountMap :=
  let elapsed := uniswapUpdateElapsedFromStorage σ ee
  let reserve0 := uniswapUpdateReserve0Word σ ee
  let reserve1 := uniswapUpdateReserve1Word σ ee
  let σP0 := uniswapUpdatePrice0CumulativeMap σ ee
  let price1 := uniswapUpdatePrice1CumulativeWord σP0 ee elapsed reserve0 reserve1
  sstoreAccountMap ee.codeOwner σP0 ⟨10⟩ price1

abbrev uniswapUpdatePrice0CumulativeMapWith
    (σ : AccountMap) (ee : ExecutionEnv) (reserve0 reserve1 : UInt256) : AccountMap :=
  let elapsed := uniswapUpdateElapsedFromStorage σ ee
  let price0 := uniswapUpdatePrice0CumulativeWord σ ee elapsed reserve1 reserve0
  sstoreAccountMap ee.codeOwner σ ⟨9⟩ price0

abbrev uniswapUpdatePrice1CumulativeMapWith
    (σ : AccountMap) (ee : ExecutionEnv) (reserve0 reserve1 : UInt256) : AccountMap :=
  let elapsed := uniswapUpdateElapsedFromStorage σ ee
  let σP0 := uniswapUpdatePrice0CumulativeMapWith σ ee reserve0 reserve1
  let price1 := uniswapUpdatePrice1CumulativeWord σP0 ee elapsed reserve0 reserve1
  sstoreAccountMap ee.codeOwner σP0 ⟨10⟩ price1

abbrev uniswapUpdateCumulativePackedWord
    (σ : AccountMap) (ee : ExecutionEnv) (balance0 balance1 : UInt256) : UInt256 :=
  let timestamp := uniswapUpdateTimestampWord ee
  let σP1 := uniswapUpdatePrice1CumulativeMap σ ee
  uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σP1 ee) timestamp balance1 balance0

abbrev uniswapUpdateCumulativePackedWordWith
    (σ : AccountMap) (ee : ExecutionEnv) (balance0 balance1 reserve0 reserve1 : UInt256) :
    UInt256 :=
  let timestamp := uniswapUpdateTimestampWord ee
  let σP1 := uniswapUpdatePrice1CumulativeMapWith σ ee reserve0 reserve1
  uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σP1 ee) timestamp balance1 balance0

abbrev uniswapUpdateCumulativePackedMap
    (σ : AccountMap) (ee : ExecutionEnv) (balance0 balance1 : UInt256) : AccountMap :=
  sstoreAccountMap ee.codeOwner (uniswapUpdatePrice1CumulativeMap σ ee) ⟨8⟩
    (uniswapUpdateCumulativePackedWord σ ee balance0 balance1)

abbrev uniswapUpdateCumulativePackedMapWith
    (σ : AccountMap) (ee : ExecutionEnv) (balance0 balance1 reserve0 reserve1 : UInt256) :
    AccountMap :=
  sstoreAccountMap ee.codeOwner (uniswapUpdatePrice1CumulativeMapWith σ ee reserve0 reserve1)
    ⟨8⟩ (uniswapUpdateCumulativePackedWordWith σ ee balance0 balance1 reserve0 reserve1)

abbrev uniswapUpdateCumulativeReturnMap
    (σ : AccountMap) (ee : ExecutionEnv) (balance0 balance1 : UInt256) : AccountMap :=
  sstoreAccountMap ee.codeOwner (uniswapUpdateCumulativePackedMap σ ee balance0 balance1)
    ⟨12⟩ ⟨1⟩

abbrev uniswapUpdateCumulativeReturnMapWith
    (σ : AccountMap) (ee : ExecutionEnv) (balance0 balance1 reserve0 reserve1 : UInt256) :
    AccountMap :=
  sstoreAccountMap ee.codeOwner
    (uniswapUpdateCumulativePackedMapWith σ ee balance0 balance1 reserve0 reserve1) ⟨12⟩
    ⟨1⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapUQ112Encode {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {value ret : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨8460⟩
      (value :: ret :: R) mem aw rdata acc k C)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret
      (uniswapUpdateEncodedUQ112 value :: R) mem aw rdata acc k' C' := by
  have rd8477 := evm_run h with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨112⟩, shl, sub, and,
    push1 ⟨1⟩, push1 ⟨112⟩, shl, mul, swap1]
  exact ⟨_, _, by
    simpa [uniswapUpdateEncodedUQ112, reserve112Mask, reserve112Shift] using
      rd8477.jump (by decide) hret (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapUQ112Div {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {denominator numerator ret : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨8478⟩
      (denominator :: numerator :: ret :: R) mem aw rdata acc k C)
    (hdenom : UInt256.land denominator reserve112Mask ≠ ⟨0⟩)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret
      (UInt256.div (UInt256.land numerator reserve224Mask)
        (UInt256.land denominator reserve112Mask) :: R)
      mem aw rdata acc k' C' := by
  have hdenomLit :
      UInt256.land denominator
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩) ≠
        ⟨0⟩ := by
    simpa [reserve112Mask, reserve112Shift] using hdenom
  have rd8505₀ := evm_run h with [
    jumpdest, push1 ⟨0⟩, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨112⟩, shl, sub,
    dup3, and, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨224⟩, shl, sub, dup5, and,
    dup2, push2 ⟨8507⟩]
  have rd8507 := evm_run rd8505₀ with [jumpiT hdenomLit (by jump_dest)]
  have rd8514 := evm_run rd8507 with [jumpdest, div, swap4, swap3, pop, pop, pop]
  exact ⟨_, _, by
    simpa [reserve224Mask, reserve224Shift, reserve112Mask, reserve112Shift] using
      rd8514.jump (by decide) hret (by evm_ov)⟩

set_option maxHeartbeats 2000000 in
theorem RD.uniswapUpdateCumulativesAndJump {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {reserve1 reserve0 balance1 balance0 : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7060⟩
      (reserve1 :: reserve0 :: balance1 :: balance0 :: R) mem aw rdata acc k C)
    (helapsedNe :
      UInt256.land (uniswapUpdateElapsedFromStorage acc.2 ee) reserve32Mask ≠ ⟨0⟩)
    (hreserve0Ne : UInt256.land reserve0 reserve112Mask ≠ ⟨0⟩)
    (hreserve1Ne : UInt256.land reserve1 reserve112Mask ≠ ⟨0⟩)
    (hperm : ee.perm = true)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C',
      let elapsed := uniswapUpdateElapsedFromStorage acc.2 ee
      let timestamp := UInt256.land reserve32Mask (UInt256.ofNat ee.header.timestamp)
      let price0 := uniswapUpdatePrice0CumulativeWord acc.2 ee elapsed reserve1 reserve0
      let σP0 := sstoreAccountMap ee.codeOwner acc.2 ⟨9⟩ price0
      let price1 := uniswapUpdatePrice1CumulativeWord σP0 ee elapsed reserve0 reserve1
      RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7241⟩
        (elapsed :: timestamp :: reserve1 :: reserve0 :: balance1 :: balance0 :: R)
        mem aw rdata (acc.1, sstoreAccountMap ee.codeOwner σP0 ⟨10⟩ price1) k' C' := by
  have helapsedLit :
      UInt256.land
        (UInt256.sub (UInt256.land reserve32Mask (UInt256.ofNat ee.header.timestamp))
          (UInt256.land reserve32Mask
            (UInt256.div
              (acc.2.find? ee.codeOwner |>.option ⟨0⟩
                (fun ac => ac.storage.findD ⟨8⟩ ⟨0⟩))
              reserve224Shift)))
        reserve32Mask ≠ ⟨0⟩ := by
    simpa [uniswapUpdateElapsedFromStorage] using helapsedNe
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
    isZero_eq_zero_of_ne helapsedLit
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
  have hreserve1NeLit :
      UInt256.land reserve1
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩) ≠
        ⟨0⟩ := by
    simpa [reserve112Mask, reserve112Shift] using hreserve1Ne
  have hreserve1IsZero :
      UInt256.isZero
        (UInt256.land reserve1
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)) =
        ⟨0⟩ :=
    isZero_eq_zero_of_ne hreserve1NeLit
  have rd7063 := evm_run h with [jumpdest, push1 ⟨8⟩]
  obtain ⟨_, _, rd7064⟩ := rd7063.sload (by decide +native)
    (by simp only [List.length_cons]; omega)
  have rd7069 := evm_run rd7064 with [push4 ⟨4294967295⟩]
  have rd7070 := RD.timestamp rd7069 (by decide +native) (by evm_ov)
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
  rw [hreserve1IsZero, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd7128
  have rd7130 := evm_run rd7128 with [jumpdest, iszero, push2 ⟨7241⟩]
  have rd7134 := evm_run rd7130 with [jumpiNT (by decide)]
  let elapsed := uniswapUpdateElapsedFromStorage acc.2 ee
  let timestamp := UInt256.land reserve32Mask (UInt256.ofNat ee.header.timestamp)
  let elapsedMasked := UInt256.land elapsed reserve32Mask
  let price0 := uniswapUpdateUQ112Price reserve1 reserve0
  let cumulative0 := uniswapUpdatePrice0CumulativeWord acc.2 ee elapsed reserve1 reserve0
  let σP0 := sstoreAccountMap ee.codeOwner acc.2 ⟨9⟩ cumulative0
  let price1 := uniswapUpdateUQ112Price reserve0 reserve1
  let cumulative1 := uniswapUpdatePrice1CumulativeWord σP0 ee elapsed reserve0 reserve1
  have rd8460₀ := evm_run rd7134 with [
    dup1, push4 ⟨4294967295⟩, and, push2 ⟨7174⟩, dup6, push2 ⟨7153⟩,
    dup7, push2 ⟨8460⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd7153₀⟩ :=
    RD.uniswapUQ112Encode rd8460₀ (by jump_dest)
      (by simp only [List.length_cons]; omega)
  have rd8478₀ := evm_run rd7153₀ with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨224⟩, shl, sub, and,
    swap1, push4 ⟨4294967295⟩, push2 ⟨8478⟩, and, jump (by jump_dest)]
  obtain ⟨_, _, rd7174⟩ :=
    RD.uniswapUQ112Div rd8478₀ hreserve0Ne (by jump_dest)
      (by simp only [List.length_cons]; omega)
  have rd7178 := evm_run rd7174 with [jumpdest, push1 ⟨9⟩, dup1]
  obtain ⟨_, _, rd7179⟩ := rd7178.sload (by decide +native)
    (by simp only [List.length_cons]; omega)
  have rd7197 := evm_run rd7179 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨224⟩, shl, sub, swap3, swap1, swap3,
    and, swap3, swap1, swap3, mul, add, swap1]
  obtain ⟨_, _, rd7198⟩ := rd7197.sstore hperm (by decide +native)
    (by simp only [List.length_cons]; omega)
  have rd8460₁ := evm_run rd7198 with [
    push4 ⟨4294967295⟩, dup2, and, push2 ⟨7217⟩, dup5, push2 ⟨7153⟩,
    dup8, push2 ⟨8460⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd7153₁⟩ :=
    RD.uniswapUQ112Encode rd8460₁ (by jump_dest)
      (by simp only [List.length_cons]; omega)
  have rd8478₁ := evm_run rd7153₁ with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨224⟩, shl, sub, and,
    swap1, push4 ⟨4294967295⟩, push2 ⟨8478⟩, and, jump (by jump_dest)]
  obtain ⟨_, _, rd7217⟩ :=
    RD.uniswapUQ112Div rd8478₁ hreserve1Ne (by jump_dest)
      (by simp only [List.length_cons]; omega)
  have rd7221 := evm_run rd7217 with [jumpdest, push1 ⟨10⟩, dup1]
  obtain ⟨_, _, rd7222⟩ := rd7221.sload (by decide +native)
    (by simp only [List.length_cons]; omega)
  have rd7240 := evm_run rd7222 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨224⟩, shl, sub, swap3, swap1, swap3,
    and, swap3, swap1, swap3, mul, add, swap1]
  obtain ⟨k7241, C7241, rd7241⟩ := rd7240.sstore hperm (by decide +native)
    (by simp only [List.length_cons]; omega)
  have hpc7241 :
      ((⟨7217⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
        UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        (⟨7241⟩ : UInt256) := by
    decide +native
  exact ⟨k7241, C7241, by
    simpa [hpc7241, elapsed, timestamp, elapsedMasked, price0, price1, cumulative0, cumulative1,
      σP0, uniswapUpdateElapsedFromStorage, uniswapUpdatePrice0CumulativeWord,
      uniswapUpdatePrice1CumulativeWord, uniswapUpdateUQ112Price, uniswapUpdateEncodedUQ112,
      reserve224Mask, reserve224Shift, reserve112Mask, reserve112Shift, reserve32Mask,
      uniswapSlotWord] using rd7241⟩

theorem uint112Mask_idempotent (w : UInt256) :
    UInt256.land (UInt256.land w reserve112Mask) reserve112Mask =
      UInt256.land w reserve112Mask := by
  apply u256_inj
  rw [uniswapUint112Masked_toNat, Nat.mod_eq_of_lt (uniswapUint112Masked_lt w)]

theorem wordOfInt_nat_mod_twoPow256 (n : Nat) :
    EVM.wordOfInt (Int.ofNat n % twoPow256) = UInt256.ofNat n := by
  rw [wordOfInt_nonneg]
  · apply u256_inj
    show (Int.toNat (Int.ofNat n % twoPow256) % UInt256.size) =
      (UInt256.ofNat n).toNat
    rw [show (Int.ofNat n % twoPow256).toNat = n % UInt256.size by
      apply Nat.cast_injective (R := Int)
      rw [Int.toNat_of_nonneg]
      · norm_num [twoPow256, UInt256.size]
      · exact Int.emod_nonneg _ (by norm_num [twoPow256])]
    show n % UInt256.size % UInt256.size = (Fin.ofNat UInt256.size n).val
    simp [Fin.ofNat]
  · exact Int.emod_nonneg _ (by norm_num [twoPow256])

theorem cumulativeIntNatForm (slot reserveNum reserveDen elapsed : Nat) :
    (Int.ofNat slot +
        (Int.ofNat reserveNum * q112 / Int.ofNat reserveDen) * Int.ofNat elapsed) %
        twoPow256 =
      Int.ofNat (slot + (reserveNum * 2 ^ 112 / reserveDen) * elapsed) %
        twoPow256 := by
  norm_num [q112]

theorem uniswapUpdateUQ112Price_toNat
    (numerator denominator : UInt256)
    (hnumerator : numerator.toNat < 2 ^ 112)
    (hdenominator : denominator.toNat < 2 ^ 112) :
    (uniswapUpdateUQ112Price numerator denominator).toNat =
      numerator.toNat * 2 ^ 112 / denominator.toNat := by
  unfold uniswapUpdateUQ112Price uniswapUpdateEncodedUQ112
  rw [udiv_toNat]
  have hmask112n : (UInt256.land reserve112Mask numerator).toNat = numerator.toNat := by
    rw [u256_land_comm]
    rw [uniswapUint112Masked_toNat]
    exact Nat.mod_eq_of_lt hnumerator
  have hmask112d : (UInt256.land denominator reserve112Mask).toNat = denominator.toNat := by
    rw [uniswapUint112Masked_toNat]
    exact Nat.mod_eq_of_lt hdenominator
  have hshift : reserve112Shift.toNat = 2 ^ 112 := by decide +native
  have hprodLt224 : 2 ^ 112 * numerator.toNat < 2 ^ 224 := by
    calc
      2 ^ 112 * numerator.toNat < 2 ^ 112 * 2 ^ 112 :=
        Nat.mul_lt_mul_of_pos_left hnumerator (by norm_num)
      _ = 2 ^ 224 := by norm_num [show 224 = 112 + 112 by omega, pow_add]
  have hprodLtSize : 2 ^ 112 * numerator.toNat < UInt256.size :=
    lt_trans hprodLt224 (by norm_num [UInt256.size])
  have hencodedToNat :
      (UInt256.mul reserve112Shift (UInt256.land reserve112Mask numerator)).toNat =
        2 ^ 112 * numerator.toNat := by
    rw [u256_mul_toNat, hshift, hmask112n, Nat.mod_eq_of_lt hprodLtSize]
  have hland224 :
      (UInt256.land reserve224Mask
          (UInt256.mul reserve112Shift (UInt256.land reserve112Mask numerator))).toNat =
        2 ^ 112 * numerator.toNat := by
    rw [u256_land_comm]
    rw [u256_land_toNat]
    have hmask : reserve224Mask.toNat = 2 ^ 224 - 1 := by decide +native
    rw [hmask, nat_land_mask_eq_mod, hencodedToNat]
    rw [Nat.mod_eq_of_lt hprodLt224]
    exact Nat.mod_eq_of_lt hprodLtSize
  have hland224₂ :
      (UInt256.land
            (UInt256.land reserve224Mask
              (UInt256.mul reserve112Shift (UInt256.land reserve112Mask numerator)))
            reserve224Mask).toNat =
        2 ^ 112 * numerator.toNat := by
    rw [u256_land_toNat]
    have hmask : reserve224Mask.toNat = 2 ^ 224 - 1 := by decide +native
    rw [hmask, nat_land_mask_eq_mod, hland224]
    rw [Nat.mod_eq_of_lt hprodLt224]
    exact Nat.mod_eq_of_lt hprodLtSize
  rw [hland224₂, hmask112d]
  rw [Nat.mul_comm]

theorem uniswapUpdatePrice0CumulativeWord_toNat
    (σ : AccountMap) (I : ExecutionEnv) (elapsed reserve1 reserve0 : UInt256)
    (hreserve1 : reserve1.toNat < 2 ^ 112)
    (hreserve0 : reserve0.toNat < 2 ^ 112) :
    (uniswapUpdatePrice0CumulativeWord σ I elapsed reserve1 reserve0).toNat =
      ((uniswapSlotWord ⟨9⟩ σ I).toNat +
        (reserve1.toNat * 2 ^ 112 / reserve0.toNat) *
          (UInt256.land reserve32Mask elapsed).toNat) % UInt256.size := by
  unfold uniswapUpdatePrice0CumulativeWord
  rw [uadd_toNat]
  rw [u256_mul_toNat]
  have hpriceToNat :=
    uniswapUpdateUQ112Price_toNat reserve1 reserve0 hreserve1 hreserve0
  have hpriceLt224 : (uniswapUpdateUQ112Price reserve1 reserve0).toNat < 2 ^ 224 := by
    rw [hpriceToNat]
    have hprodLt224 : reserve1.toNat * 2 ^ 112 < 2 ^ 224 := by
      calc
        reserve1.toNat * 2 ^ 112 < 2 ^ 112 * 2 ^ 112 :=
          Nat.mul_lt_mul_of_pos_right hreserve1 (by norm_num)
        _ = 2 ^ 224 := by norm_num [show 224 = 112 + 112 by omega, pow_add]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) hprodLt224
  have hpriceNatLt : reserve1.toNat * 2 ^ 112 / reserve0.toNat < 2 ^ 224 := by
    simpa [hpriceToNat] using hpriceLt224
  have hpriceLand :
      (UInt256.land reserve224Mask (uniswapUpdateUQ112Price reserve1 reserve0)).toNat =
        reserve1.toNat * 2 ^ 112 / reserve0.toNat := by
    rw [u256_land_comm]
    rw [u256_land_toNat]
    have hmask : reserve224Mask.toNat = 2 ^ 224 - 1 := by decide +native
    rw [hmask, nat_land_mask_eq_mod, hpriceToNat]
    rw [Nat.mod_eq_of_lt hpriceNatLt]
    exact Nat.mod_eq_of_lt (lt_trans hpriceNatLt (by norm_num [UInt256.size]))
  have helapsedLt : (UInt256.land reserve32Mask elapsed).toNat < 2 ^ 32 := by
    simpa [u256_land_comm] using uniswapUint32Masked_lt elapsed
  have hmulLtSize :
      (reserve1.toNat * 2 ^ 112 / reserve0.toNat) *
          (UInt256.land reserve32Mask elapsed).toNat < UInt256.size := by
    calc
      (reserve1.toNat * 2 ^ 112 / reserve0.toNat) *
          (UInt256.land reserve32Mask elapsed).toNat < 2 ^ 224 * 2 ^ 32 :=
        Nat.mul_lt_mul'' hpriceNatLt helapsedLt
      _ = UInt256.size := by
        norm_num [UInt256.size, show 256 = 224 + 32 by omega, pow_add]
  rw [hpriceLand, Nat.mod_eq_of_lt hmulLtSize]
  rw [Nat.add_comm]

theorem uniswapUpdatePrice1CumulativeWord_toNat
    (σ : AccountMap) (I : ExecutionEnv) (elapsed reserve0 reserve1 : UInt256)
    (hreserve0 : reserve0.toNat < 2 ^ 112)
    (hreserve1 : reserve1.toNat < 2 ^ 112) :
    (uniswapUpdatePrice1CumulativeWord σ I elapsed reserve0 reserve1).toNat =
      ((uniswapSlotWord ⟨10⟩ σ I).toNat +
        (reserve0.toNat * 2 ^ 112 / reserve1.toNat) *
          (UInt256.land elapsed reserve32Mask).toNat) % UInt256.size := by
  unfold uniswapUpdatePrice1CumulativeWord
  rw [uadd_toNat]
  rw [u256_mul_toNat]
  have hpriceToNat :=
    uniswapUpdateUQ112Price_toNat reserve0 reserve1 hreserve0 hreserve1
  have hpriceLt224 : (uniswapUpdateUQ112Price reserve0 reserve1).toNat < 2 ^ 224 := by
    rw [hpriceToNat]
    have hprodLt224 : reserve0.toNat * 2 ^ 112 < 2 ^ 224 := by
      calc
        reserve0.toNat * 2 ^ 112 < 2 ^ 112 * 2 ^ 112 :=
          Nat.mul_lt_mul_of_pos_right hreserve0 (by norm_num)
        _ = 2 ^ 224 := by norm_num [show 224 = 112 + 112 by omega, pow_add]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) hprodLt224
  have hpriceNatLt : reserve0.toNat * 2 ^ 112 / reserve1.toNat < 2 ^ 224 := by
    simpa [hpriceToNat] using hpriceLt224
  have hpriceLand :
      (UInt256.land reserve224Mask (uniswapUpdateUQ112Price reserve0 reserve1)).toNat =
        reserve0.toNat * 2 ^ 112 / reserve1.toNat := by
    rw [u256_land_comm]
    rw [u256_land_toNat]
    have hmask : reserve224Mask.toNat = 2 ^ 224 - 1 := by decide +native
    rw [hmask, nat_land_mask_eq_mod, hpriceToNat]
    rw [Nat.mod_eq_of_lt hpriceNatLt]
    exact Nat.mod_eq_of_lt (lt_trans hpriceNatLt (by norm_num [UInt256.size]))
  have helapsedLt : (UInt256.land elapsed reserve32Mask).toNat < 2 ^ 32 :=
    uniswapUint32Masked_lt elapsed
  have hmulLtSize :
      (reserve0.toNat * 2 ^ 112 / reserve1.toNat) *
          (UInt256.land elapsed reserve32Mask).toNat < UInt256.size := by
    calc
      (reserve0.toNat * 2 ^ 112 / reserve1.toNat) *
          (UInt256.land elapsed reserve32Mask).toNat < 2 ^ 224 * 2 ^ 32 :=
        Nat.mul_lt_mul'' hpriceNatLt helapsedLt
      _ = UInt256.size := by
        norm_num [UInt256.size, show 256 = 224 + 32 by omega, pow_add]
  rw [hpriceLand, Nat.mod_eq_of_lt hmulLtSize]
  rw [Nat.add_comm]

theorem syncPrice0CumulativeIntAt_eq_updateWord_nat_form
    {σStorage σUpdate : AccountMap} {storageEvm updateEvm : EVM.State}
    {I : ExecutionEnv} {elapsed reserve1 reserve0 : UInt256}
    (hStorageAccounts : accountMapEquiv σStorage storageEvm.accountMap)
    (hStorageEnv : storageEvm.executionEnv = I)
    (hUpdateEnv : updateEvm.executionEnv = I)
    (hslot8 :
      Solm.EVM.storageLoad updateEvm updateEvm.executionEnv.codeOwner ⟨8⟩ =
        uniswapSlotWord ⟨8⟩ σUpdate I)
    (helapsed : elapsed = uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σUpdate I) I)
    (hreserve1 :
      reserve1 =
        UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σUpdate I) reserve112Shift)
          reserve112Mask)
    (hreserve0 :
      reserve0 = UInt256.land (uniswapSlotWord ⟨8⟩ σUpdate I) reserve112Mask) :
    syncPrice0CumulativeIntAt storageEvm updateEvm =
      Int.ofNat ((uniswapSlotWord ⟨9⟩ σStorage I).toNat +
        (reserve1.toNat * 2 ^ 112 / reserve0.toNat) *
          (UInt256.land reserve32Mask elapsed).toNat) % twoPow256 := by
  have hslot9 :
      Solm.EVM.storageLoad storageEvm storageEvm.executionEnv.codeOwner ⟨9⟩ =
        uniswapSlotWord ⟨9⟩ σStorage I := by
    have h := accountMapEquiv_storage_findD hStorageAccounts I.codeOwner ⟨9⟩ ⟨0⟩
    simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, uniswapSlotWord,
      hStorageEnv] at h ⊢
    exact h.symm
  have hslot8I :
      Solm.EVM.storageLoad updateEvm I.codeOwner ⟨8⟩ =
        uniswapSlotWord ⟨8⟩ σUpdate I := by
    simpa [hUpdateEnv] using hslot8
  have htime :
      syncTimeElapsedInt updateEvm =
        Int.ofNat (UInt256.land reserve32Mask elapsed).toNat := by
    rw [syncTimeElapsedInt_eq_updateElapsedWord_toNat updateEvm]
    subst elapsed
    simpa [hslot8I, hUpdateEnv, u256_land_comm]
  have hres0word : uniswapReserve0Word updateEvm = reserve0 := by
    subst reserve0
    simp [uniswapReserve0Word, hslot8]
  have hres1word : uniswapReserve1Word updateEvm = reserve1 := by
    subst reserve1
    simp [uniswapReserve1Word, hslot8]
  unfold syncPrice0CumulativeIntAt
  rw [hslot9, hres0word, hres1word, htime]
  simpa using
    cumulativeIntNatForm (uniswapSlotWord ⟨9⟩ σStorage I).toNat reserve1.toNat
      reserve0.toNat (UInt256.land reserve32Mask elapsed).toNat

theorem syncPrice1CumulativeIntAt_eq_updateWord_nat_form
    {σStorage σUpdate : AccountMap} {storageEvm updateEvm : EVM.State}
    {I : ExecutionEnv} {elapsed reserve0 reserve1 : UInt256}
    (hStorageAccounts : accountMapEquiv σStorage storageEvm.accountMap)
    (hStorageEnv : storageEvm.executionEnv = I)
    (hUpdateEnv : updateEvm.executionEnv = I)
    (hslot8 :
      Solm.EVM.storageLoad updateEvm updateEvm.executionEnv.codeOwner ⟨8⟩ =
        uniswapSlotWord ⟨8⟩ σUpdate I)
    (helapsed : elapsed = uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σUpdate I) I)
    (hreserve0 :
      reserve0 = UInt256.land (uniswapSlotWord ⟨8⟩ σUpdate I) reserve112Mask)
    (hreserve1 :
      reserve1 =
        UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σUpdate I) reserve112Shift)
          reserve112Mask) :
    syncPrice1CumulativeIntAt storageEvm updateEvm =
      Int.ofNat ((uniswapSlotWord ⟨10⟩ σStorage I).toNat +
        (reserve0.toNat * 2 ^ 112 / reserve1.toNat) *
          (UInt256.land elapsed reserve32Mask).toNat) % twoPow256 := by
  have hslot10 :
      Solm.EVM.storageLoad storageEvm storageEvm.executionEnv.codeOwner ⟨10⟩ =
        uniswapSlotWord ⟨10⟩ σStorage I := by
    have h := accountMapEquiv_storage_findD hStorageAccounts I.codeOwner ⟨10⟩ ⟨0⟩
    simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, uniswapSlotWord,
      hStorageEnv] at h ⊢
    exact h.symm
  have hslot8I :
      Solm.EVM.storageLoad updateEvm I.codeOwner ⟨8⟩ =
        uniswapSlotWord ⟨8⟩ σUpdate I := by
    simpa [hUpdateEnv] using hslot8
  have htime :
      syncTimeElapsedInt updateEvm =
        Int.ofNat (UInt256.land elapsed reserve32Mask).toNat := by
    rw [syncTimeElapsedInt_eq_updateElapsedWord_toNat updateEvm]
    subst elapsed
    simpa [hslot8I, hUpdateEnv]
  have hres0word : uniswapReserve0Word updateEvm = reserve0 := by
    subst reserve0
    simp [uniswapReserve0Word, hslot8]
  have hres1word : uniswapReserve1Word updateEvm = reserve1 := by
    subst reserve1
    simp [uniswapReserve1Word, hslot8]
  unfold syncPrice1CumulativeIntAt
  rw [hslot10, hres0word, hres1word, htime]
  simpa using
    cumulativeIntNatForm (uniswapSlotWord ⟨10⟩ σStorage I).toNat reserve0.toNat
      reserve1.toNat (UInt256.land elapsed reserve32Mask).toNat

theorem accountMapEquiv_syncUpdatePackedReserveState
    {σ : AccountMap} {evm : EVM.State} {I : ExecutionEnv}
    {balance0 balance1 packed : UInt256}
    (hPost : accountMapEquiv σ evm.accountMap)
    (henv : evm.executionEnv = I)
    (hslot :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ =
        uniswapSlotWord ⟨8⟩ σ I)
    (hpacked :
      packed =
        uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σ I)
          (uniswapUpdateTimestampWord I) balance1 balance0) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner σ ⟨8⟩ packed)
      (syncUpdatePackedReserveState evm balance0 balance1).accountMap := by
  let v0 := setUint112Offset0Word (uniswapSlotWord ⟨8⟩ σ I) balance0
  let v1 := setUint112Offset14Word v0 balance1
  have hpacked' : packed = setUint32Offset28Word v1 (uniswapUpdateTimestampWord I) := by
    simp [hpacked, v0, v1, uniswapUpdatePackedReserveWord_eq_setters]
  by_cases haccExists : ∃ acc, evm.accountMap.find? I.codeOwner = some acc
  · obtain ⟨acc, hacc⟩ := haccExists
    have hload0 :
        Solm.EVM.storageLoad evm I.codeOwner ⟨8⟩ = uniswapSlotWord ⟨8⟩ σ I := by
      simpa [henv] using hslot
    have hload1 :
        Solm.EVM.storageLoad
            (Solm.EVM.storageStore evm I.codeOwner ⟨8⟩ v0)
            I.codeOwner ⟨8⟩ =
          v0 := by
      exact storageLoad_storageStore_same_present evm I.codeOwner hacc ⟨8⟩ v0
    obtain ⟨acc0, hacc0⟩ :
        ∃ acc0,
          (Solm.EVM.storageStore evm I.codeOwner ⟨8⟩ v0).accountMap.find? I.codeOwner =
            some acc0 := by
      refine ⟨Account.updateStorage acc ⟨8⟩ v0, ?_⟩
      simpa [Solm.EVM.storageStore, State.lookupAccount, hacc, State.setAccount,
        Option.option] using
        accountMap_find_insert_self evm.accountMap I.codeOwner
          (Account.updateStorage acc ⟨8⟩ v0)
    have hload2 :
        Solm.EVM.storageLoad
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm I.codeOwner ⟨8⟩ v0)
              I.codeOwner ⟨8⟩ v1)
            I.codeOwner ⟨8⟩ =
          v1 := by
      exact storageLoad_storageStore_same_present
        (Solm.EVM.storageStore evm I.codeOwner ⟨8⟩ v0) I.codeOwner hacc0 ⟨8⟩ v1
    have hbase :
        accountMapEquiv
          (sstoreAccountMap I.codeOwner σ ⟨8⟩ packed)
          (sstoreAccountMap I.codeOwner evm.accountMap ⟨8⟩ packed) :=
      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨8⟩ packed hPost
    have hsingle :
        accountMapEquiv
          (sstoreAccountMap I.codeOwner evm.accountMap ⟨8⟩ packed)
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner evm.accountMap ⟨8⟩ v1) ⟨8⟩ packed) :=
      accountMapEquiv_sstoreAccountMap_self_update evm.accountMap I.codeOwner ⟨8⟩ v1
        packed
    have hupdate01 :
        accountMapEquiv
          (sstoreAccountMap I.codeOwner evm.accountMap ⟨8⟩ v1)
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner evm.accountMap ⟨8⟩ v0) ⟨8⟩ v1) :=
      accountMapEquiv_sstoreAccountMap_self_update evm.accountMap I.codeOwner ⟨8⟩ v0 v1
    have hdouble :
        accountMapEquiv
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner evm.accountMap ⟨8⟩ v1) ⟨8⟩ packed)
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner evm.accountMap ⟨8⟩ v0) ⟨8⟩ v1)
            ⟨8⟩ packed) :=
      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨8⟩ packed hupdate01
    have hchain := (hbase.trans hsingle).trans hdouble
    simpa [syncUpdatePackedReserveState, storageStore_accountMap, storageStore_executionEnv,
      hload0, hload1, hload2, henv, hpacked', v0, v1] using hchain
  · have hmissing : evm.accountMap.find? I.codeOwner = none := by
      cases hfind : evm.accountMap.find? I.codeOwner with
      | none => rfl
      | some acc => exact False.elim (haccExists ⟨acc, hfind⟩)
    have hmissingSource : σ.find? I.codeOwner = none :=
      accountMapEquiv_find?_none hPost.symm hmissing
    have hleft : sstoreAccountMap I.codeOwner σ ⟨8⟩ packed = σ :=
      sstoreAccountMap_absent_same hmissingSource
    have hmissingOwner : evm.accountMap.find? evm.executionEnv.codeOwner = none := by
      simpa [henv] using hmissing
    have hright :
        (syncUpdatePackedReserveState evm balance0 balance1).accountMap =
          evm.accountMap := by
      simp [syncUpdatePackedReserveState,
        storageStore_absent evm evm.executionEnv.codeOwner hmissingOwner]
    simpa [hleft, hright] using hPost

theorem uniswapStorageLocStore_word_int (evm : EVM.State) (slot : UInt256) (n : Int) :
    storageLocStore evm (wordLoc slot) (.int n) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot (EVM.wordOfInt n)) := by
  unfold storageLocStore storageLocWriteWord wordLoc
  simp only [valueToWord, bind, Option.bind, pure]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof (EVM.wordOfInt n)).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (32 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (32 : Fin 33).val) _) =
      (EVM.wordOfInt n).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (32 : Fin 33).val = 32 from rfl,
    List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by rw [hslen]),
    List.append_nil, List.take_of_length_le (by rw [hvlen]), fromBytes'_toBytesLEWithSizeProof]

abbrev syncUpdateCumulativePackedReserveState
    (evm : EVM.State) (balance0 balance1 : UInt256) : EVM.State :=
  let evmP0 :=
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨9⟩
      (EVM.wordOfInt (syncPrice0CumulativeIntAt evm evm))
  let evmP1 :=
    Solm.EVM.storageStore evmP0 evmP0.executionEnv.codeOwner ⟨10⟩
      (EVM.wordOfInt (syncPrice1CumulativeIntAt evmP0 evm))
  let evmR0 :=
    Solm.EVM.storageStore evmP1 evmP1.executionEnv.codeOwner ⟨8⟩
      (setUint112Offset0Word
        (Solm.EVM.storageLoad evmP1 evmP1.executionEnv.codeOwner ⟨8⟩) balance0)
  let evmR1 :=
    Solm.EVM.storageStore evmR0 evmR0.executionEnv.codeOwner ⟨8⟩
      (setUint112Offset14Word
        (Solm.EVM.storageLoad evmR0 evmR0.executionEnv.codeOwner ⟨8⟩) balance1)
  Solm.EVM.storageStore evmR1 evmR1.executionEnv.codeOwner ⟨8⟩
    (setUint32Offset28Word
      (Solm.EVM.storageLoad evmR1 evmR1.executionEnv.codeOwner ⟨8⟩)
      (uniswapUpdateTimestampWord evm.executionEnv))

abbrev syncPrice0CumulativeIntAtWith
    (storageEvm updateEvm : EVM.State) (reserve0 reserve1 : UInt256) : Int :=
  (Int.ofNat (Solm.EVM.storageLoad storageEvm storageEvm.executionEnv.codeOwner ⟨9⟩).toNat +
    ((Int.ofNat reserve1.toNat * q112) / Int.ofNat reserve0.toNat) *
        syncTimeElapsedInt updateEvm) % twoPow256

abbrev syncPrice0CumulativeValueAtWith
    (storageEvm updateEvm : EVM.State) (reserve0 reserve1 : UInt256) : Value :=
  .int (syncPrice0CumulativeIntAtWith storageEvm updateEvm reserve0 reserve1)

abbrev syncPrice1CumulativeIntAtWith
    (storageEvm updateEvm : EVM.State) (reserve0 reserve1 : UInt256) : Int :=
  (Int.ofNat (Solm.EVM.storageLoad storageEvm storageEvm.executionEnv.codeOwner ⟨10⟩).toNat +
    ((Int.ofNat reserve0.toNat * q112) / Int.ofNat reserve1.toNat) *
        syncTimeElapsedInt updateEvm) % twoPow256

abbrev syncPrice1CumulativeValueAtWith
    (storageEvm updateEvm : EVM.State) (reserve0 reserve1 : UInt256) : Value :=
  .int (syncPrice1CumulativeIntAtWith storageEvm updateEvm reserve0 reserve1)

abbrev syncUpdateCumulativePackedReserveStateWith
    (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256) : EVM.State :=
  let evmP0 :=
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨9⟩
      (EVM.wordOfInt (syncPrice0CumulativeIntAtWith evm evm reserve0 reserve1))
  let evmP1 :=
    Solm.EVM.storageStore evmP0 evmP0.executionEnv.codeOwner ⟨10⟩
      (EVM.wordOfInt (syncPrice1CumulativeIntAtWith evmP0 evm reserve0 reserve1))
  let evmR0 :=
    Solm.EVM.storageStore evmP1 evmP1.executionEnv.codeOwner ⟨8⟩
      (setUint112Offset0Word
        (Solm.EVM.storageLoad evmP1 evmP1.executionEnv.codeOwner ⟨8⟩) balance0)
  let evmR1 :=
    Solm.EVM.storageStore evmR0 evmR0.executionEnv.codeOwner ⟨8⟩
      (setUint112Offset14Word
        (Solm.EVM.storageLoad evmR0 evmR0.executionEnv.codeOwner ⟨8⟩) balance1)
  Solm.EVM.storageStore evmR1 evmR1.executionEnv.codeOwner ⟨8⟩
    (setUint32Offset28Word
      (Solm.EVM.storageLoad evmR1 evmR1.executionEnv.codeOwner ⟨8⟩)
      (uniswapUpdateTimestampWord evm.executionEnv))

theorem evalExpr_sync_update_price0Cumulative_with
    (storageEvm updateEvm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256)
    (hreserve0 : Int.ofNat reserve0.toNat ≠ 0) :
    evalExpr? config
      { contract := contract,
        locals := syncUpdateTimeElapsedStoreWith updateEvm balance0 balance1 reserve0
          reserve1 }
      storageEvm
      (wrapU256 (.binary .add (.storage price0CumulativeLastRef)
        (.binary .mul (uq112Price (.var "_reserve1") (.var "_reserve0"))
          (.var "timeElapsed")))) =
        .ok (syncPrice0CumulativeValueAtWith storageEvm updateEvm reserve0 reserve1) := by
  have hreserve0Nat : reserve0.toNat ≠ 0 := by
    intro hzero
    exact hreserve0 (by simp [hzero])
  unfold wrapU256 uq112Price syncPrice0CumulativeValueAtWith
    syncPrice0CumulativeIntAtWith
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind,
    evalExpr_sync_price0CumulativeLast storageEvm
      (syncUpdateTimeElapsedStoreWith updateEvm balance0 balance1 reserve0 reserve1)
      (syncUpdateTimeElapsedStoreWith_price0CumulativeLast_none updateEvm balance0 balance1
        reserve0 reserve1),
    syncUpdateTimeElapsedStoreWith_reserve1, syncUpdateTimeElapsedStoreWith_reserve0,
    syncUpdateTimeElapsedStoreWith_timeElapsed]
  unfold syncTimeElapsedValue
  simp [evalBinaryOp?, hreserve0Nat, twoPow256]

theorem evalExpr_sync_update_price1Cumulative_with
    (storageEvm updateEvm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256)
    (hreserve1 : Int.ofNat reserve1.toNat ≠ 0) :
    evalExpr? config
      { contract := contract,
        locals := syncUpdateTimeElapsedStoreWith updateEvm balance0 balance1 reserve0
          reserve1 }
      storageEvm
      (wrapU256 (.binary .add (.storage price1CumulativeLastRef)
        (.binary .mul (uq112Price (.var "_reserve0") (.var "_reserve1"))
          (.var "timeElapsed")))) =
        .ok (syncPrice1CumulativeValueAtWith storageEvm updateEvm reserve0 reserve1) := by
  have hreserve1Nat : reserve1.toNat ≠ 0 := by
    intro hzero
    exact hreserve1 (by simp [hzero])
  unfold wrapU256 uq112Price syncPrice1CumulativeValueAtWith
    syncPrice1CumulativeIntAtWith
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind,
    evalExpr_sync_price1CumulativeLast storageEvm
      (syncUpdateTimeElapsedStoreWith updateEvm balance0 balance1 reserve0 reserve1)
      (syncUpdateTimeElapsedStoreWith_price1CumulativeLast_none updateEvm balance0 balance1
        reserve0 reserve1),
    syncUpdateTimeElapsedStoreWith_reserve0, syncUpdateTimeElapsedStoreWith_reserve1,
    syncUpdateTimeElapsedStoreWith_timeElapsed]
  unfold syncTimeElapsedValue
  simp [evalBinaryOp?, hreserve1Nat, twoPow256]

set_option maxHeartbeats 1000000 in
theorem uniswapUpdateFunctionReturns_conditionTrue_packed
    (evm : EVM.State) (balance0 balance1 : UInt256)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed : 0 < syncTimeElapsedInt evm)
    (hreserve0 : Int.ofNat (uniswapReserve0Word evm).toNat ≠ 0)
    (hreserve1 : Int.ofNat (uniswapReserve1Word evm).toNat ≠ 0) :
    ExecFuncBody config (syncUpdateCallFrame evm balance0 balance1) evm
      updateFunction.body
      (.returned
        { contract := contract, locals := syncUpdateTimeElapsedStore evm balance0 balance1 }
        (syncUpdateCumulativePackedReserveState evm balance0 balance1) none) := by
  let evmP0 :=
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨9⟩
      (EVM.wordOfInt (syncPrice0CumulativeIntAt evm evm))
  let evmP1 :=
    Solm.EVM.storageStore evmP0 evmP0.executionEnv.codeOwner ⟨10⟩
      (EVM.wordOfInt (syncPrice1CumulativeIntAt evmP0 evm))
  let evmR0 :=
    Solm.EVM.storageStore evmP1 evmP1.executionEnv.codeOwner ⟨8⟩
      (setUint112Offset0Word
        (Solm.EVM.storageLoad evmP1 evmP1.executionEnv.codeOwner ⟨8⟩) balance0)
  let evmR1 :=
    Solm.EVM.storageStore evmR0 evmR0.executionEnv.codeOwner ⟨8⟩
      (setUint112Offset14Word
        (Solm.EVM.storageLoad evmR0 evmR0.executionEnv.codeOwner ⟨8⟩) balance1)
  have hstoreP0 :
      storageLocStore evm (wordLoc ⟨9⟩) (syncPrice0CumulativeValueAt evm evm) =
        some evmP0 := by
    simpa [evmP0, syncPrice0CumulativeValueAt] using
      uniswapStorageLocStore_word_int evm ⟨9⟩ (syncPrice0CumulativeIntAt evm evm)
  have hstoreP1 :
      storageLocStore evmP0 (wordLoc ⟨10⟩) (syncPrice1CumulativeValueAt evmP0 evm) =
        some evmP1 := by
    simpa [evmP1, syncPrice1CumulativeValueAt] using
      uniswapStorageLocStore_word_int evmP0 ⟨10⟩ (syncPrice1CumulativeIntAt evmP0 evm)
  have hstoreR0 :
      storageLocStore evmP1 (uint112Loc0 ⟨8⟩) (uniswapUint256Value balance0) =
        some evmR0 := by
    simpa [evmR0] using uniswapStorageLocStore_uint112_offset0 evmP1 ⟨8⟩ balance0
  have hstoreR1 :
      storageLocStore evmR0 (uint112Loc14 ⟨8⟩) (uniswapUint256Value balance1) =
        some evmR1 := by
    simpa [evmR1] using uniswapStorageLocStore_uint112_offset14 evmR0 ⟨8⟩ balance1
  have hstoreTs :
      storageLocStore evmR1 (uint32Loc28 ⟨8⟩) (syncBlockTimestampValue evm) =
        some (syncUpdateCumulativePackedReserveState evm balance0 balance1) := by
    rw [syncBlockTimestampValue_eq_updateTimestampWord evm]
    simpa [syncUpdateCumulativePackedReserveState, evmP0, evmP1, evmR0, evmR1] using
      uniswapStorageLocStore_uint32_offset28 evmR1 ⟨8⟩
        (uniswapUpdateTimestampWord evm.executionEnv)
  refine ExecFuncBody.execBlockOK ?_
  change ExecBlock config (syncUpdateCallFrame evm balance0 balance1) evm
    [ .require (.binary .and
        (.binary .le (.var "balance0") (.intLit maxUint112))
        (.binary .le (.var "balance1") (.intLit maxUint112))),
      .letDecl "blockTimestamp" (some uint32) (u32 (.binary .mod now (.intLit twoPow32))),
      .letDecl "timeElapsed" (some uint32)
        (u32 (.binary .mod
          (.binary .add
            (.binary .sub (.var "blockTimestamp") (.storage blockTimestampLastRef))
            (.intLit twoPow32))
          (.intLit twoPow32))),
      .ite (.binary .and
          (.binary .gt (.var "timeElapsed") (.intLit 0))
          (.binary .and
            (.binary .ne (.var "_reserve0") (.intLit 0))
            (.binary .ne (.var "_reserve1") (.intLit 0))))
        [ .assign .storage price0CumulativeLastRef
            (wrapU256 (.binary .add (.storage price0CumulativeLastRef)
              (.binary .mul (uq112Price (.var "_reserve1") (.var "_reserve0"))
                (.var "timeElapsed")))),
          .assign .storage price1CumulativeLastRef
            (wrapU256 (.binary .add (.storage price1CumulativeLastRef)
              (.binary .mul (uq112Price (.var "_reserve0") (.var "_reserve1"))
                (.var "timeElapsed")))) ]
        [],
      .assign .storage reserve0Ref (u112 (.var "balance0")),
      .assign .storage reserve1Ref (u112 (.var "balance1")),
      .assign .storage blockTimestampLastRef (.var "blockTimestamp") ]
    (.ok { contract := contract, locals := syncUpdateTimeElapsedStore evm balance0 balance1 }
      (syncUpdateCumulativePackedReserveState evm balance0 balance1))
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_sync_update_bounds_true evm balance0 balance1 hbound0 hbound1)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_sync_update_blockTimestamp evm balance0 balance1)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_sync_update_timeElapsed evm balance0 balance1)) ?_
  have hpriceBlock :
      ExecBlock config
        { contract := contract, locals := syncUpdateTimeElapsedStore evm balance0 balance1 } evm
        [ .assign .storage price0CumulativeLastRef
            (wrapU256 (.binary .add (.storage price0CumulativeLastRef)
              (.binary .mul (uq112Price (.var "_reserve1") (.var "_reserve0"))
                (.var "timeElapsed")))),
          .assign .storage price1CumulativeLastRef
            (wrapU256 (.binary .add (.storage price1CumulativeLastRef)
              (.binary .mul (uq112Price (.var "_reserve0") (.var "_reserve1"))
                (.var "timeElapsed")))) ]
        (.ok { contract := contract, locals := syncUpdateTimeElapsedStore evm balance0 balance1 }
          evmP1) := by
    refine ExecBlock.consNormal
      (ExecStmt.assign
        (evalExpr_sync_update_price0Cumulative evm evm balance0 balance1 hreserve0)
        (uniswapAssignPrice0CumulativeLastOfStore evm evmP0
          (syncUpdateTimeElapsedStore evm balance0 balance1)
          (syncPrice0CumulativeValueAt evm evm)
          (syncUpdateTimeElapsedStore_price0CumulativeLast_none evm balance0 balance1)
          (by simp)
          hstoreP0)) ?_
    exact ExecBlock.consNormal
      (ExecStmt.assign
        (evalExpr_sync_update_price1Cumulative evmP0 evm balance0 balance1 hreserve1)
        (uniswapAssignPrice1CumulativeLastOfStore evmP0 evmP1
          (syncUpdateTimeElapsedStore evm balance0 balance1)
          (syncPrice1CumulativeValueAt evmP0 evm)
          (syncUpdateTimeElapsedStore_price1CumulativeLast_none evm balance0 balance1)
          (by simp)
          hstoreP1))
      ExecBlock.nil
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue
      (evalExpr_sync_update_condition_true evm balance0 balance1 helapsed hreserve0 hreserve1)
      hpriceBlock) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_sync_update_u112_balance0 evm evmP1 balance0 balance1 hbound0)
      (uniswapAssignReserve0OfStore evmP1 evmR0
        (syncUpdateTimeElapsedStore evm balance0 balance1) balance0
        (syncUpdateTimeElapsedStore_reserve0_none evm balance0 balance1)
        hstoreR0)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_sync_update_u112_balance1 evm evmR0 balance0 balance1 hbound1)
      (uniswapAssignReserve1OfStore evmR0 evmR1
        (syncUpdateTimeElapsedStore evm balance0 balance1) balance1
        (syncUpdateTimeElapsedStore_reserve1_none evm balance0 balance1)
        hstoreR1)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_sync_update_blockTimestamp_var evmR1 evm balance0 balance1)
      (uniswapAssignBlockTimestampLastOfStore evmR1
        (syncUpdateCumulativePackedReserveState evm balance0 balance1)
        (syncUpdateTimeElapsedStore evm balance0 balance1) (syncBlockTimestampValue evm)
        (syncUpdateTimeElapsedStore_blockTimestampLast_none evm balance0 balance1)
        (by simp)
        hstoreTs))
    ExecBlock.nil

set_option maxHeartbeats 1000000 in
theorem uniswapUpdateFunctionReturns_conditionTrue_packed_with
    (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed : 0 < syncTimeElapsedInt evm)
    (hreserve0 : Int.ofNat reserve0.toNat ≠ 0)
    (hreserve1 : Int.ofNat reserve1.toNat ≠ 0) :
    ExecFuncBody config (syncUpdateCallFrameWith balance0 balance1 reserve0 reserve1) evm
      updateFunction.body
      (.returned
        { contract := contract,
          locals := syncUpdateTimeElapsedStoreWith evm balance0 balance1 reserve0 reserve1 }
        (syncUpdateCumulativePackedReserveStateWith evm balance0 balance1 reserve0 reserve1)
        none) := by
  let evmP0 :=
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨9⟩
      (EVM.wordOfInt (syncPrice0CumulativeIntAtWith evm evm reserve0 reserve1))
  let evmP1 :=
    Solm.EVM.storageStore evmP0 evmP0.executionEnv.codeOwner ⟨10⟩
      (EVM.wordOfInt (syncPrice1CumulativeIntAtWith evmP0 evm reserve0 reserve1))
  let evmR0 :=
    Solm.EVM.storageStore evmP1 evmP1.executionEnv.codeOwner ⟨8⟩
      (setUint112Offset0Word
        (Solm.EVM.storageLoad evmP1 evmP1.executionEnv.codeOwner ⟨8⟩) balance0)
  let evmR1 :=
    Solm.EVM.storageStore evmR0 evmR0.executionEnv.codeOwner ⟨8⟩
      (setUint112Offset14Word
        (Solm.EVM.storageLoad evmR0 evmR0.executionEnv.codeOwner ⟨8⟩) balance1)
  have hstoreP0 :
      storageLocStore evm (wordLoc ⟨9⟩)
          (syncPrice0CumulativeValueAtWith evm evm reserve0 reserve1) =
        some evmP0 := by
    simpa [evmP0, syncPrice0CumulativeValueAtWith] using
      uniswapStorageLocStore_word_int evm ⟨9⟩
        (syncPrice0CumulativeIntAtWith evm evm reserve0 reserve1)
  have hstoreP1 :
      storageLocStore evmP0 (wordLoc ⟨10⟩)
          (syncPrice1CumulativeValueAtWith evmP0 evm reserve0 reserve1) =
        some evmP1 := by
    simpa [evmP1, syncPrice1CumulativeValueAtWith] using
      uniswapStorageLocStore_word_int evmP0 ⟨10⟩
        (syncPrice1CumulativeIntAtWith evmP0 evm reserve0 reserve1)
  have hstoreR0 :
      storageLocStore evmP1 (uint112Loc0 ⟨8⟩) (uniswapUint256Value balance0) =
        some evmR0 := by
    simpa [evmR0] using uniswapStorageLocStore_uint112_offset0 evmP1 ⟨8⟩ balance0
  have hstoreR1 :
      storageLocStore evmR0 (uint112Loc14 ⟨8⟩) (uniswapUint256Value balance1) =
        some evmR1 := by
    simpa [evmR1] using uniswapStorageLocStore_uint112_offset14 evmR0 ⟨8⟩ balance1
  have hstoreTs :
      storageLocStore evmR1 (uint32Loc28 ⟨8⟩) (syncBlockTimestampValue evm) =
        some (syncUpdateCumulativePackedReserveStateWith evm balance0 balance1 reserve0
          reserve1) := by
    rw [syncBlockTimestampValue_eq_updateTimestampWord evm]
    simpa [syncUpdateCumulativePackedReserveStateWith, evmP0, evmP1, evmR0, evmR1] using
      uniswapStorageLocStore_uint32_offset28 evmR1 ⟨8⟩
        (uniswapUpdateTimestampWord evm.executionEnv)
  refine ExecFuncBody.execBlockOK ?_
  change ExecBlock config (syncUpdateCallFrameWith balance0 balance1 reserve0 reserve1) evm
    [ .require (.binary .and
        (.binary .le (.var "balance0") (.intLit maxUint112))
        (.binary .le (.var "balance1") (.intLit maxUint112))),
      .letDecl "blockTimestamp" (some uint32) (u32 (.binary .mod now (.intLit twoPow32))),
      .letDecl "timeElapsed" (some uint32)
        (u32 (.binary .mod
          (.binary .add
            (.binary .sub (.var "blockTimestamp") (.storage blockTimestampLastRef))
            (.intLit twoPow32))
          (.intLit twoPow32))),
      .ite (.binary .and
          (.binary .gt (.var "timeElapsed") (.intLit 0))
          (.binary .and
            (.binary .ne (.var "_reserve0") (.intLit 0))
            (.binary .ne (.var "_reserve1") (.intLit 0))))
        [ .assign .storage price0CumulativeLastRef
            (wrapU256 (.binary .add (.storage price0CumulativeLastRef)
              (.binary .mul (uq112Price (.var "_reserve1") (.var "_reserve0"))
                (.var "timeElapsed")))),
          .assign .storage price1CumulativeLastRef
            (wrapU256 (.binary .add (.storage price1CumulativeLastRef)
              (.binary .mul (uq112Price (.var "_reserve0") (.var "_reserve1"))
                (.var "timeElapsed")))) ]
        [],
      .assign .storage reserve0Ref (u112 (.var "balance0")),
      .assign .storage reserve1Ref (u112 (.var "balance1")),
      .assign .storage blockTimestampLastRef (.var "blockTimestamp") ]
    (.ok
      { contract := contract,
        locals := syncUpdateTimeElapsedStoreWith evm balance0 balance1 reserve0 reserve1 }
      (syncUpdateCumulativePackedReserveStateWith evm balance0 balance1 reserve0 reserve1))
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_sync_update_bounds_true_with evm balance0 balance1 reserve0 reserve1
        hbound0 hbound1)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl
      (evalExpr_sync_update_blockTimestamp_with evm balance0 balance1 reserve0 reserve1)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl
      (evalExpr_sync_update_timeElapsed_with evm balance0 balance1 reserve0 reserve1)) ?_
  have hpriceBlock :
      ExecBlock config
        { contract := contract,
          locals := syncUpdateTimeElapsedStoreWith evm balance0 balance1 reserve0 reserve1 }
        evm
        [ .assign .storage price0CumulativeLastRef
            (wrapU256 (.binary .add (.storage price0CumulativeLastRef)
              (.binary .mul (uq112Price (.var "_reserve1") (.var "_reserve0"))
                (.var "timeElapsed")))),
          .assign .storage price1CumulativeLastRef
            (wrapU256 (.binary .add (.storage price1CumulativeLastRef)
              (.binary .mul (uq112Price (.var "_reserve0") (.var "_reserve1"))
                (.var "timeElapsed")))) ]
        (.ok
          { contract := contract,
            locals := syncUpdateTimeElapsedStoreWith evm balance0 balance1 reserve0 reserve1 }
          evmP1) := by
    refine ExecBlock.consNormal
      (ExecStmt.assign
        (evalExpr_sync_update_price0Cumulative_with evm evm balance0 balance1 reserve0
          reserve1 hreserve0)
        (uniswapAssignPrice0CumulativeLastOfStore evm evmP0
          (syncUpdateTimeElapsedStoreWith evm balance0 balance1 reserve0 reserve1)
          (syncPrice0CumulativeValueAtWith evm evm reserve0 reserve1)
          (syncUpdateTimeElapsedStoreWith_price0CumulativeLast_none evm balance0 balance1
            reserve0 reserve1)
          (by simp)
          hstoreP0)) ?_
    exact ExecBlock.consNormal
      (ExecStmt.assign
        (evalExpr_sync_update_price1Cumulative_with evmP0 evm balance0 balance1 reserve0
          reserve1 hreserve1)
        (uniswapAssignPrice1CumulativeLastOfStore evmP0 evmP1
          (syncUpdateTimeElapsedStoreWith evm balance0 balance1 reserve0 reserve1)
          (syncPrice1CumulativeValueAtWith evmP0 evm reserve0 reserve1)
          (syncUpdateTimeElapsedStoreWith_price1CumulativeLast_none evm balance0 balance1
            reserve0 reserve1)
          (by simp)
          hstoreP1))
      ExecBlock.nil
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue
      (evalExpr_sync_update_condition_true_with evm balance0 balance1 reserve0 reserve1
        helapsed hreserve0 hreserve1)
      hpriceBlock) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_sync_update_u112_balance0_with evm evmP1 balance0 balance1 reserve0 reserve1
        hbound0)
      (uniswapAssignReserve0OfStore evmP1 evmR0
        (syncUpdateTimeElapsedStoreWith evm balance0 balance1 reserve0 reserve1) balance0
        (syncUpdateTimeElapsedStoreWith_reserve0_none evm balance0 balance1 reserve0 reserve1)
        hstoreR0)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_sync_update_u112_balance1_with evm evmR0 balance0 balance1 reserve0 reserve1
        hbound1)
      (uniswapAssignReserve1OfStore evmR0 evmR1
        (syncUpdateTimeElapsedStoreWith evm balance0 balance1 reserve0 reserve1) balance1
        (syncUpdateTimeElapsedStoreWith_reserve1_none evm balance0 balance1 reserve0 reserve1)
        hstoreR1)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_sync_update_blockTimestamp_var_with evmR1 evm balance0 balance1 reserve0
        reserve1)
      (uniswapAssignBlockTimestampLastOfStore evmR1
        (syncUpdateCumulativePackedReserveStateWith evm balance0 balance1 reserve0 reserve1)
        (syncUpdateTimeElapsedStoreWith evm balance0 balance1 reserve0 reserve1)
        (syncBlockTimestampValue evm)
        (syncUpdateTimeElapsedStoreWith_blockTimestampLast_none evm balance0 balance1 reserve0
          reserve1)
        (by simp)
        hstoreTs))
    ExecBlock.nil

theorem uniswapSyncUpdateCallReturns_conditionTrue_packed
    (evm : EVM.State) (balance0 balance1 : UInt256)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed : 0 < syncTimeElapsedInt evm)
    (hreserve0 : Int.ofNat (uniswapReserve0Word evm).toNat ≠ 0)
    (hreserve1 : Int.ofNat (uniswapReserve1Word evm).toNat ≠ 0) :
    ExecStmt config { contract := contract, locals := syncBalanceStore balance0 balance1 } evm
      (.internalCall "_update"
        [ .var "balance0", .var "balance1", .storage reserve0Ref, .storage reserve1Ref ]
        "_updateResult")
      (.ok (syncAfterUpdateFrame balance0 balance1)
        (syncUpdateCumulativePackedReserveState evm balance0 balance1)) := by
  have hbody :=
    uniswapUpdateFunctionReturns_conditionTrue_packed evm balance0 balance1
      hbound0 hbound1 helapsed hreserve0 hreserve1
  simpa [syncAfterUpdateFrame, syncAfterUpdateStore, resumeAfterInternalCall] using
    (internalCallFunctionReturn
      (cfg := config)
      (caller := { contract := contract, locals := syncBalanceStore balance0 balance1 })
      (evm := evm)
      (calleeEvm := syncUpdateCumulativePackedReserveState evm balance0 balance1)
      (name := "_update") (retVar := "_updateResult")
      (args := [ .var "balance0", .var "balance1", .storage reserve0Ref, .storage reserve1Ref ])
      (argVals := syncUpdateCallArgVals evm balance0 balance1) (callee := updateFunction)
      (locals := syncUpdateCallStore evm balance0 balance1)
      (calleeSolm :=
        { contract := contract, locals := syncUpdateTimeElapsedStore evm balance0 balance1 })
      (value := none)
      (evalExprs_sync_update_call_args evm balance0 balance1)
      uniswapLookupUpdateFunction
      (bindParams_sync_update_call evm balance0 balance1)
      hbody)

theorem uniswapSyncBodyReturns_conditionTrue_packed (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardTrue evm)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 =
      some [uniswapUint256Value balance0])
    (hguard1 : syncToken1GuardTrue evm0 (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 =
      some [uniswapUint256Value balance1])
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed : 0 < syncTimeElapsedInt evm1)
    (hreserve0 : Int.ofNat (uniswapReserve0Word evm1).toNat ≠ 0)
    (hreserve1 : Int.ofNat (uniswapReserve1Word evm1).toNat ≠ 0) :
    ExecTransitionBody config contract evm ∅ syncTransition.body
      (.returned (syncAfterUpdateFrame balance0 balance1)
        (uniswapLockExitedState (syncUpdateCumulativePackedReserveState evm1 balance0 balance1))
        none) := by
  have hbalances := uniswapSyncBalanceOfCallsPrefix
    (evm := evm) (evm0 := evm0) (evm1 := evm1)
    (balance0 := uniswapUint256Value balance0) (balance1 := uniswapUint256Value balance1)
    hwv hunlocked hguard0 hcall0 hdec0 hguard1 hcall1 hdec1
  have hupdateStmt :=
    uniswapSyncUpdateCallReturns_conditionTrue_packed evm1 balance0 balance1 hbound0
      hbound1 helapsed hreserve0 hreserve1
  have hupdateBlock :
      ExecBlock config { contract := contract, locals := syncBalanceStore balance0 balance1 } evm1
        (updateReservesStmts (.var "balance0") (.var "balance1"))
        (.ok (syncAfterUpdateFrame balance0 balance1)
          (syncUpdateCumulativePackedReserveState evm1 balance0 balance1)) := by
    simpa [updateReservesStmts] using
      (ExecBlock.consNormal hupdateStmt ExecBlock.nil)
  have hlock :=
    uniswapLockExitSuffix (syncUpdateCumulativePackedReserveState evm1 balance0 balance1)
      (syncAfterUpdateStore balance0 balance1)
      (by simp [syncAfterUpdateStore, syncBalanceStore, uniswapBalanceOfStore])
  have htail := execBlock_append hupdateBlock hlock
  have hbody := execBlock_append hbalances htail
  exact ExecFuncBody.execBlockOK
    (by
      simpa [syncTransition, syncBalanceCallsBody, updateReservesStmts, List.append_assoc]
        using hbody)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapUpdateCumulativesToReturn {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {balance0 balance1 : UInt256}
    {o o1 : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7060⟩
      [uniswapUpdateReserve1Word σ ee, uniswapUpdateReserve0Word σ ee, balance1,
        balance0, ⟨6363⟩, ⟨570⟩, uniswapSelWord ee]
      (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat ee.codeOwner.val) o o1)
      balanceOfThisStaticcallActiveWords o1 (cA, σ) k C)
    (hmemSize128 :
      128 ≤ (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat ee.codeOwner.val) o o1).size)
    (hmemRead64 :
      (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat ee.codeOwner.val) o o1).readWithPadding
          64 32 =
        UInt256.toByteArray ⟨128⟩)
    (ho32 : 32 ≤ o.size)
    (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size)
    (ho1Size : o1.size < UInt256.size)
    (helapsedNe :
      UInt256.land (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σ ee) ee)
          reserve32Mask ≠
        ⟨0⟩)
    (hreserve0Nonzero : uniswapUpdateReserve0Word σ ee ≠ ⟨0⟩)
    (hreserve1Nonzero : uniswapUpdateReserve1Word σ ee ≠ ⟨0⟩)
    (hperm : ee.perm = true) :
    RDret UniswapV2Pair.uniswapV2PairBytecode g s0
      (cA, uniswapUpdateCumulativeReturnMap σ ee balance0 balance1) ByteArray.empty := by
  have hreserve0Masked :
      UInt256.land (uniswapUpdateReserve0Word σ ee) reserve112Mask =
        uniswapUpdateReserve0Word σ ee := by
    dsimp [uniswapUpdateReserve0Word]
    exact uint112Mask_idempotent (uniswapSlotWord ⟨8⟩ σ ee)
  have hreserve1Masked :
      UInt256.land (uniswapUpdateReserve1Word σ ee) reserve112Mask =
        uniswapUpdateReserve1Word σ ee := by
    dsimp [uniswapUpdateReserve1Word]
    exact uint112Mask_idempotent
      (UInt256.div (uniswapSlotWord ⟨8⟩ σ ee) reserve112Shift)
  have hreserve0Ne :
      UInt256.land (uniswapUpdateReserve0Word σ ee) reserve112Mask ≠ ⟨0⟩ := by
    rw [hreserve0Masked]
    exact hreserve0Nonzero
  have hreserve1Ne :
      UInt256.land (uniswapUpdateReserve1Word σ ee) reserve112Mask ≠ ⟨0⟩ := by
    rw [hreserve1Masked]
    exact hreserve1Nonzero
  obtain ⟨_, _, rd7241⟩ :=
    RD.uniswapUpdateCumulativesAndJump h
      (by
        simpa [uniswapUpdateElapsedFromStorage, uniswapUpdateElapsedWord,
          uniswapUpdateTimestampWord, uniswapSlotWord] using helapsedNe)
      hreserve0Ne hreserve1Ne hperm
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd7339⟩ :=
    RD.uniswapUpdateStorePackedReserves
      (by
        simpa [uniswapUpdateReserve0Word, uniswapUpdateReserve1Word,
          uniswapUpdatePrice0CumulativeMap, uniswapUpdatePrice1CumulativeMap,
          uniswapUpdateCumulativePackedWord, uniswapUpdateCumulativePackedMap,
          uniswapUpdateElapsedFromStorage, uniswapUpdateElapsedWord,
          uniswapUpdateTimestampWord, uniswapSlotWord] using rd7241)
      hperm
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd6363⟩ :=
    RD.uniswapUpdateEmitSyncAndJump
      (packed := uniswapUpdateCumulativePackedWord σ ee balance0 balance1)
      (ret := ⟨6363⟩) (R := [⟨570⟩, uniswapSelWord ee])
      (mem := balanceOfThisRebuiltStaticcallMem (UInt256.ofNat ee.codeOwner.val) o o1)
      (aw := balanceOfThisStaticcallActiveWords)
      (awLoad := balanceOfThisStaticcallActiveWords)
      (awLog := balanceOfThisStaticcallActiveWords)
      (mcostLoad := 0) (mcostStore0 := 0) (mcostStore1 := 0)
      (mcostLoadLog := 0) (mcostLog := 0)
      (by
        simpa [uniswapUpdateReserve0Word, uniswapUpdateReserve1Word,
          uniswapUpdatePrice0CumulativeMap, uniswapUpdatePrice1CumulativeMap,
          uniswapUpdateCumulativePackedWord, uniswapUpdateCumulativePackedMap,
          uniswapUpdateElapsedFromStorage, uniswapUpdateElapsedWord,
          uniswapUpdateTimestampWord, uniswapSlotWord] using rd7339)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
        decide +native)
      (by
        exact balanceOfThisRebuiltStaticcallMem_mload64_of_size_ge
          (UInt256.ofNat ee.codeOwner.val) o o1 ho32 hoSize ho132 ho1Size)
      (by decide +native)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
        decide +native)
      (by decide +native)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
        decide +native)
      (by decide +native)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
        decide +native)
      (by
        exact uniswapSyncLogMem_mload64
          (uniswapUpdateCumulativePackedWord σ ee balance0 balance1)
          (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat ee.codeOwner.val) o o1)
          hmemSize128 hmemRead64)
      (by decide +native)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
        decide +native)
      (by decide +native) hperm (by jump_dest)
      (by simp only [List.length_cons, List.length_nil]; omega)
  simpa [uniswapUpdateCumulativeReturnMap] using
    RD.uniswapSyncAfterUpdateToReturn rd6363 hperm

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000000 in
theorem accountMapEquiv_uniswapUpdatePrice0CumulativeMap
    {σ : AccountMap} {evm : EVM.State} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ evm.accountMap)
    (henv : evm.executionEnv = I)
    (hslot8 :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ =
        uniswapSlotWord ⟨8⟩ σ I) :
    accountMapEquiv (uniswapUpdatePrice0CumulativeMap σ I)
      (Solm.EVM.storageStore evm I.codeOwner ⟨9⟩
        (EVM.wordOfInt (syncPrice0CumulativeIntAt evm evm))).accountMap := by
  let reserve0Word : UInt256 := uniswapUpdateReserve0Word σ I
  let reserve1Word : UInt256 := uniswapUpdateReserve1Word σ I
  let elapsedWord : UInt256 := uniswapUpdateElapsedFromStorage σ I
  let price0Word : UInt256 :=
    uniswapUpdatePrice0CumulativeWord σ I elapsedWord reserve1Word reserve0Word
  have helapsedSource :
      elapsedWord = uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σ I) I := by
    simp [elapsedWord, uniswapUpdateElapsedFromStorage, uniswapUpdateElapsedWord,
      uniswapUpdateTimestampWord, uniswapSlotWord]
  have hprice0Nat :
      syncPrice0CumulativeIntAt evm evm =
        Int.ofNat ((uniswapSlotWord ⟨9⟩ σ I).toNat +
          (reserve1Word.toNat * 2 ^ 112 / reserve0Word.toNat) *
            (UInt256.land reserve32Mask elapsedWord).toNat) %
          twoPow256 := by
    exact syncPrice0CumulativeIntAt_eq_updateWord_nat_form
      (σStorage := σ) (σUpdate := σ)
      (storageEvm := evm) (updateEvm := evm)
      (I := I) (elapsed := elapsedWord)
      (reserve1 := reserve1Word) (reserve0 := reserve0Word)
      hAccounts henv henv hslot8 helapsedSource (by rfl) (by rfl)
  have hprice0Eq :
      EVM.wordOfInt (syncPrice0CumulativeIntAt evm evm) = price0Word := by
    let n : Nat := (uniswapSlotWord ⟨9⟩ σ I).toNat +
      (reserve1Word.toNat * 2 ^ 112 / reserve0Word.toNat) *
        (UInt256.land reserve32Mask elapsedWord).toNat
    have hn : syncPrice0CumulativeIntAt evm evm = Int.ofNat n % twoPow256 := by
      simpa [n] using hprice0Nat
    have hprice0ToNat : price0Word.toNat = n % UInt256.size := by
      simpa [price0Word, n] using
        uniswapUpdatePrice0CumulativeWord_toNat σ I elapsedWord reserve1Word reserve0Word
          (by
            dsimp [reserve1Word, uniswapUpdateReserve1Word]
            exact uniswapUint112Masked_lt _)
          (by
            dsimp [reserve0Word, uniswapUpdateReserve0Word]
            exact uniswapUint112Masked_lt _)
    have hsync : syncPrice0CumulativeIntAt evm evm = Int.ofNat price0Word.toNat := by
      rw [hn, hprice0ToNat]
      norm_num [UInt256.size, twoPow256]
    rw [hsync]
    exact wordOfInt_ofNat_toNat price0Word
  have hs := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨9⟩ price0Word hAccounts
  simpa [uniswapUpdatePrice0CumulativeMap, reserve0Word, reserve1Word, elapsedWord,
    price0Word, storageStore_accountMap, hprice0Eq] using hs

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000000 in
theorem accountMapEquiv_uniswapUpdatePrice1CumulativeMap
    {σ : AccountMap} {evm : EVM.State} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ evm.accountMap)
    (henv : evm.executionEnv = I)
    (hslot8 :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ =
        uniswapSlotWord ⟨8⟩ σ I) :
    let evmP0 :=
      Solm.EVM.storageStore evm I.codeOwner ⟨9⟩
        (EVM.wordOfInt (syncPrice0CumulativeIntAt evm evm))
    accountMapEquiv (uniswapUpdatePrice1CumulativeMap σ I)
      (Solm.EVM.storageStore evmP0 I.codeOwner ⟨10⟩
        (EVM.wordOfInt (syncPrice1CumulativeIntAt evmP0 evm))).accountMap := by
  let evmP0 :=
    Solm.EVM.storageStore evm I.codeOwner ⟨9⟩
      (EVM.wordOfInt (syncPrice0CumulativeIntAt evm evm))
  let reserve0Word : UInt256 := uniswapUpdateReserve0Word σ I
  let reserve1Word : UInt256 := uniswapUpdateReserve1Word σ I
  let elapsedWord : UInt256 := uniswapUpdateElapsedFromStorage σ I
  let σP0 : AccountMap := uniswapUpdatePrice0CumulativeMap σ I
  let price1Word : UInt256 :=
    uniswapUpdatePrice1CumulativeWord σP0 I elapsedWord reserve0Word reserve1Word
  have hP0Accounts : accountMapEquiv σP0 evmP0.accountMap := by
    simpa [σP0, evmP0] using
      accountMapEquiv_uniswapUpdatePrice0CumulativeMap hAccounts henv hslot8
  have henvP0 : evmP0.executionEnv = I := by
    simp [evmP0, storageStore_executionEnv, henv]
  have helapsedSource :
      elapsedWord = uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σ I) I := by
    simp [elapsedWord, uniswapUpdateElapsedFromStorage, uniswapUpdateElapsedWord,
      uniswapUpdateTimestampWord, uniswapSlotWord]
  have hprice1Nat :
      syncPrice1CumulativeIntAt evmP0 evm =
        Int.ofNat ((uniswapSlotWord ⟨10⟩ σP0 I).toNat +
          (reserve0Word.toNat * 2 ^ 112 / reserve1Word.toNat) *
            (UInt256.land elapsedWord reserve32Mask).toNat) %
          twoPow256 := by
    exact syncPrice1CumulativeIntAt_eq_updateWord_nat_form
      (σStorage := σP0) (σUpdate := σ)
      (storageEvm := evmP0) (updateEvm := evm)
      (I := I) (elapsed := elapsedWord)
      (reserve0 := reserve0Word) (reserve1 := reserve1Word)
      hP0Accounts henvP0 henv hslot8 helapsedSource (by rfl) (by rfl)
  have hprice1Eq :
      EVM.wordOfInt (syncPrice1CumulativeIntAt evmP0 evm) = price1Word := by
    let n : Nat := (uniswapSlotWord ⟨10⟩ σP0 I).toNat +
      (reserve0Word.toNat * 2 ^ 112 / reserve1Word.toNat) *
        (UInt256.land elapsedWord reserve32Mask).toNat
    have hn : syncPrice1CumulativeIntAt evmP0 evm = Int.ofNat n % twoPow256 := by
      simpa [n] using hprice1Nat
    have hprice1ToNat : price1Word.toNat = n % UInt256.size := by
      simpa [price1Word, n] using
        uniswapUpdatePrice1CumulativeWord_toNat σP0 I elapsedWord reserve0Word reserve1Word
          (by
            dsimp [reserve0Word, uniswapUpdateReserve0Word]
            exact uniswapUint112Masked_lt _)
          (by
            dsimp [reserve1Word, uniswapUpdateReserve1Word]
            exact uniswapUint112Masked_lt _)
    have hsync :
        syncPrice1CumulativeIntAt evmP0 evm = Int.ofNat price1Word.toNat := by
      rw [hn, hprice1ToNat]
      norm_num [UInt256.size, twoPow256]
    rw [hsync]
    exact wordOfInt_ofNat_toNat price1Word
  have hs := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨10⟩ price1Word hP0Accounts
  simpa [uniswapUpdatePrice1CumulativeMap, σP0, reserve0Word, reserve1Word, evmP0,
    elapsedWord, price1Word, storageStore_accountMap, hprice1Eq] using hs

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000000 in
theorem accountMapEquiv_syncUpdateCumulativeReturnMap
    {σ : AccountMap} {evm : EVM.State} {I : ExecutionEnv} {balance0 balance1 : UInt256}
    (hAccounts : accountMapEquiv σ evm.accountMap)
    (henv : evm.executionEnv = I)
    (hslot8 :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ =
        uniswapSlotWord ⟨8⟩ σ I) :
    accountMapEquiv (uniswapUpdateCumulativeReturnMap σ I balance0 balance1)
      (uniswapLockExitedState
        (syncUpdateCumulativePackedReserveState evm balance0 balance1)).accountMap := by
  let evmP0 :=
    Solm.EVM.storageStore evm I.codeOwner ⟨9⟩
      (EVM.wordOfInt (syncPrice0CumulativeIntAt evm evm))
  let evmP1 :=
    Solm.EVM.storageStore evmP0 I.codeOwner ⟨10⟩
      (EVM.wordOfInt (syncPrice1CumulativeIntAt evmP0 evm))
  let σP1 : AccountMap := uniswapUpdatePrice1CumulativeMap σ I
  let packedCumulative : UInt256 := uniswapUpdateCumulativePackedWord σ I balance0 balance1
  have hP1Accounts : accountMapEquiv σP1 evmP1.accountMap := by
    simpa [σP1, evmP0, evmP1] using
      accountMapEquiv_uniswapUpdatePrice1CumulativeMap hAccounts henv hslot8
  have henvP0 : evmP0.executionEnv = I := by
    simp [evmP0, storageStore_executionEnv, henv]
  have henvP1 : evmP1.executionEnv = I := by
    simp [evmP1, storageStore_executionEnv, henvP0]
  have hslot8P1 :
      Solm.EVM.storageLoad evmP1 evmP1.executionEnv.codeOwner ⟨8⟩ =
        uniswapSlotWord ⟨8⟩ σP1 I := by
    have h := accountMapEquiv_storage_findD hP1Accounts I.codeOwner ⟨8⟩ ⟨0⟩
    simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
      uniswapSlotWord, henvP1] at h ⊢
    exact h.symm
  have hPackedAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σP1 ⟨8⟩ packedCumulative)
        (syncUpdatePackedReserveState evmP1 balance0 balance1).accountMap :=
    accountMapEquiv_syncUpdatePackedReserveState hP1Accounts henvP1 hslot8P1
      (by simp [packedCumulative, uniswapUpdateCumulativePackedWord, σP1])
  have hPackedAccountsCumulative :
      accountMapEquiv (uniswapUpdateCumulativePackedMap σ I balance0 balance1)
        (syncUpdateCumulativePackedReserveState evm balance0 balance1).accountMap := by
    simpa [uniswapUpdateCumulativePackedMap, uniswapUpdateCumulativePackedWord,
      syncUpdateCumulativePackedReserveState, syncUpdatePackedReserveState, evmP0, evmP1,
      σP1, packedCumulative, storageStore_executionEnv, henv, henvP0] using hPackedAccounts
  have hReturnAccounts :=
    accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨1⟩ hPackedAccountsCumulative
  simpa [uniswapUpdateCumulativeReturnMap, uniswapLockExitedState, uniswapUnlockedState,
    storageStore_accountMap, storageStore_executionEnv, syncUpdateCumulativePackedReserveState,
    henv] using hReturnAccounts

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000000 in
theorem accountMapEquiv_uniswapUpdatePrice0CumulativeMapWith
    {σ : AccountMap} {evm : EVM.State} {I : ExecutionEnv} {reserve0 reserve1 : UInt256}
    (hAccounts : accountMapEquiv σ evm.accountMap)
    (henv : evm.executionEnv = I)
    (hslot8 :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ =
        uniswapSlotWord ⟨8⟩ σ I)
    (hreserve0Lt : reserve0.toNat < 2 ^ 112)
    (hreserve1Lt : reserve1.toNat < 2 ^ 112) :
    accountMapEquiv (uniswapUpdatePrice0CumulativeMapWith σ I reserve0 reserve1)
      (Solm.EVM.storageStore evm I.codeOwner ⟨9⟩
        (EVM.wordOfInt
          (syncPrice0CumulativeIntAtWith evm evm reserve0 reserve1))).accountMap := by
  let elapsedWord : UInt256 := uniswapUpdateElapsedFromStorage σ I
  let price0Word : UInt256 :=
    uniswapUpdatePrice0CumulativeWord σ I elapsedWord reserve1 reserve0
  have hslot9 :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨9⟩ =
        uniswapSlotWord ⟨9⟩ σ I := by
    have h := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨9⟩ ⟨0⟩
    simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, uniswapSlotWord,
      henv] at h ⊢
    exact h.symm
  have hslot8I :
      Solm.EVM.storageLoad evm I.codeOwner ⟨8⟩ =
        uniswapSlotWord ⟨8⟩ σ I := by
    simpa [henv] using hslot8
  have htime :
      syncTimeElapsedInt evm =
        Int.ofNat (UInt256.land reserve32Mask elapsedWord).toNat := by
    rw [syncTimeElapsedInt_eq_updateElapsedWord_toNat evm]
    simp [elapsedWord, uniswapUpdateElapsedFromStorage, uniswapUpdateElapsedWord,
      uniswapUpdateTimestampWord, uniswapSlotWord, hslot8I, henv, u256_land_comm]
  have hprice0Nat :
      syncPrice0CumulativeIntAtWith evm evm reserve0 reserve1 =
        Int.ofNat ((uniswapSlotWord ⟨9⟩ σ I).toNat +
          (reserve1.toNat * 2 ^ 112 / reserve0.toNat) *
            (UInt256.land reserve32Mask elapsedWord).toNat) %
          twoPow256 := by
    unfold syncPrice0CumulativeIntAtWith
    rw [hslot9, htime]
    simpa using
      cumulativeIntNatForm (uniswapSlotWord ⟨9⟩ σ I).toNat reserve1.toNat
        reserve0.toNat (UInt256.land reserve32Mask elapsedWord).toNat
  have hprice0Eq :
      EVM.wordOfInt (syncPrice0CumulativeIntAtWith evm evm reserve0 reserve1) =
        price0Word := by
    let n : Nat := (uniswapSlotWord ⟨9⟩ σ I).toNat +
      (reserve1.toNat * 2 ^ 112 / reserve0.toNat) *
        (UInt256.land reserve32Mask elapsedWord).toNat
    have hn :
        syncPrice0CumulativeIntAtWith evm evm reserve0 reserve1 =
          Int.ofNat n % twoPow256 := by
      simpa [n] using hprice0Nat
    have hprice0ToNat : price0Word.toNat = n % UInt256.size := by
      simpa [price0Word, n] using
        uniswapUpdatePrice0CumulativeWord_toNat σ I elapsedWord reserve1 reserve0
          hreserve1Lt hreserve0Lt
    have hsync :
        syncPrice0CumulativeIntAtWith evm evm reserve0 reserve1 =
          Int.ofNat price0Word.toNat := by
      rw [hn, hprice0ToNat]
      norm_num [UInt256.size, twoPow256]
    rw [hsync]
    exact wordOfInt_ofNat_toNat price0Word
  have hs := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨9⟩ price0Word hAccounts
  simpa [uniswapUpdatePrice0CumulativeMapWith, elapsedWord, price0Word,
    storageStore_accountMap, hprice0Eq] using hs

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000000 in
theorem accountMapEquiv_uniswapUpdatePrice1CumulativeMapWith
    {σ : AccountMap} {evm : EVM.State} {I : ExecutionEnv} {reserve0 reserve1 : UInt256}
    (hAccounts : accountMapEquiv σ evm.accountMap)
    (henv : evm.executionEnv = I)
    (hslot8 :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ =
        uniswapSlotWord ⟨8⟩ σ I)
    (hreserve0Lt : reserve0.toNat < 2 ^ 112)
    (hreserve1Lt : reserve1.toNat < 2 ^ 112) :
    let evmP0 :=
      Solm.EVM.storageStore evm I.codeOwner ⟨9⟩
        (EVM.wordOfInt (syncPrice0CumulativeIntAtWith evm evm reserve0 reserve1))
    accountMapEquiv (uniswapUpdatePrice1CumulativeMapWith σ I reserve0 reserve1)
      (Solm.EVM.storageStore evmP0 I.codeOwner ⟨10⟩
        (EVM.wordOfInt
          (syncPrice1CumulativeIntAtWith evmP0 evm reserve0 reserve1))).accountMap := by
  let evmP0 :=
    Solm.EVM.storageStore evm I.codeOwner ⟨9⟩
      (EVM.wordOfInt (syncPrice0CumulativeIntAtWith evm evm reserve0 reserve1))
  let elapsedWord : UInt256 := uniswapUpdateElapsedFromStorage σ I
  let σP0 : AccountMap := uniswapUpdatePrice0CumulativeMapWith σ I reserve0 reserve1
  let price1Word : UInt256 :=
    uniswapUpdatePrice1CumulativeWord σP0 I elapsedWord reserve0 reserve1
  have hP0Accounts : accountMapEquiv σP0 evmP0.accountMap := by
    simpa [σP0, evmP0] using
      accountMapEquiv_uniswapUpdatePrice0CumulativeMapWith
        hAccounts henv hslot8 hreserve0Lt hreserve1Lt
  have henvP0 : evmP0.executionEnv = I := by
    simp [evmP0, storageStore_executionEnv, henv]
  have hslot10 :
      Solm.EVM.storageLoad evmP0 evmP0.executionEnv.codeOwner ⟨10⟩ =
        uniswapSlotWord ⟨10⟩ σP0 I := by
    have h := accountMapEquiv_storage_findD hP0Accounts I.codeOwner ⟨10⟩ ⟨0⟩
    simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, uniswapSlotWord,
      henvP0] at h ⊢
    exact h.symm
  have hslot8I :
      Solm.EVM.storageLoad evm I.codeOwner ⟨8⟩ =
        uniswapSlotWord ⟨8⟩ σ I := by
    simpa [henv] using hslot8
  have htime :
      syncTimeElapsedInt evm =
        Int.ofNat (UInt256.land elapsedWord reserve32Mask).toNat := by
    rw [syncTimeElapsedInt_eq_updateElapsedWord_toNat evm]
    simp [elapsedWord, uniswapUpdateElapsedFromStorage, uniswapUpdateElapsedWord,
      uniswapUpdateTimestampWord, uniswapSlotWord, hslot8I, henv]
  have hprice1Nat :
      syncPrice1CumulativeIntAtWith evmP0 evm reserve0 reserve1 =
        Int.ofNat ((uniswapSlotWord ⟨10⟩ σP0 I).toNat +
          (reserve0.toNat * 2 ^ 112 / reserve1.toNat) *
            (UInt256.land elapsedWord reserve32Mask).toNat) %
          twoPow256 := by
    unfold syncPrice1CumulativeIntAtWith
    rw [hslot10, htime]
    simpa using
      cumulativeIntNatForm (uniswapSlotWord ⟨10⟩ σP0 I).toNat reserve0.toNat
        reserve1.toNat (UInt256.land elapsedWord reserve32Mask).toNat
  have hprice1Eq :
      EVM.wordOfInt (syncPrice1CumulativeIntAtWith evmP0 evm reserve0 reserve1) =
        price1Word := by
    let n : Nat := (uniswapSlotWord ⟨10⟩ σP0 I).toNat +
      (reserve0.toNat * 2 ^ 112 / reserve1.toNat) *
        (UInt256.land elapsedWord reserve32Mask).toNat
    have hn :
        syncPrice1CumulativeIntAtWith evmP0 evm reserve0 reserve1 =
          Int.ofNat n % twoPow256 := by
      simpa [n] using hprice1Nat
    have hprice1ToNat : price1Word.toNat = n % UInt256.size := by
      simpa [price1Word, n] using
        uniswapUpdatePrice1CumulativeWord_toNat σP0 I elapsedWord reserve0 reserve1
          hreserve0Lt hreserve1Lt
    have hsync :
        syncPrice1CumulativeIntAtWith evmP0 evm reserve0 reserve1 =
          Int.ofNat price1Word.toNat := by
      rw [hn, hprice1ToNat]
      norm_num [UInt256.size, twoPow256]
    rw [hsync]
    exact wordOfInt_ofNat_toNat price1Word
  have hs := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨10⟩ price1Word hP0Accounts
  simpa [uniswapUpdatePrice1CumulativeMapWith, σP0, evmP0, elapsedWord, price1Word,
    storageStore_accountMap, hprice1Eq] using hs

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000000 in
theorem accountMapEquiv_syncUpdateCumulativeReturnMapWith
    {σ : AccountMap} {evm : EVM.State} {I : ExecutionEnv}
    {balance0 balance1 reserve0 reserve1 : UInt256}
    (hAccounts : accountMapEquiv σ evm.accountMap)
    (henv : evm.executionEnv = I)
    (hslot8 :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ =
        uniswapSlotWord ⟨8⟩ σ I)
    (hreserve0Lt : reserve0.toNat < 2 ^ 112)
    (hreserve1Lt : reserve1.toNat < 2 ^ 112) :
    accountMapEquiv
      (uniswapUpdateCumulativeReturnMapWith σ I balance0 balance1 reserve0 reserve1)
      (uniswapLockExitedState
        (syncUpdateCumulativePackedReserveStateWith
          evm balance0 balance1 reserve0 reserve1)).accountMap := by
  let evmP0 :=
    Solm.EVM.storageStore evm I.codeOwner ⟨9⟩
      (EVM.wordOfInt (syncPrice0CumulativeIntAtWith evm evm reserve0 reserve1))
  let evmP1 :=
    Solm.EVM.storageStore evmP0 I.codeOwner ⟨10⟩
      (EVM.wordOfInt (syncPrice1CumulativeIntAtWith evmP0 evm reserve0 reserve1))
  let σP1 : AccountMap := uniswapUpdatePrice1CumulativeMapWith σ I reserve0 reserve1
  let packedCumulative : UInt256 :=
    uniswapUpdateCumulativePackedWordWith σ I balance0 balance1 reserve0 reserve1
  have hP1Accounts : accountMapEquiv σP1 evmP1.accountMap := by
    simpa [σP1, evmP0, evmP1] using
      accountMapEquiv_uniswapUpdatePrice1CumulativeMapWith
        hAccounts henv hslot8 hreserve0Lt hreserve1Lt
  have henvP0 : evmP0.executionEnv = I := by
    simp [evmP0, storageStore_executionEnv, henv]
  have henvP1 : evmP1.executionEnv = I := by
    simp [evmP1, storageStore_executionEnv, henvP0]
  have hslot8P1 :
      Solm.EVM.storageLoad evmP1 evmP1.executionEnv.codeOwner ⟨8⟩ =
        uniswapSlotWord ⟨8⟩ σP1 I := by
    have h := accountMapEquiv_storage_findD hP1Accounts I.codeOwner ⟨8⟩ ⟨0⟩
    simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
      uniswapSlotWord, henvP1] at h ⊢
    exact h.symm
  have hPackedAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σP1 ⟨8⟩ packedCumulative)
        (syncUpdatePackedReserveState evmP1 balance0 balance1).accountMap :=
    accountMapEquiv_syncUpdatePackedReserveState hP1Accounts henvP1 hslot8P1
      (by simp [packedCumulative, uniswapUpdateCumulativePackedWordWith, σP1])
  have hPackedAccountsCumulative :
      accountMapEquiv
        (uniswapUpdateCumulativePackedMapWith σ I balance0 balance1 reserve0 reserve1)
        (syncUpdateCumulativePackedReserveStateWith
          evm balance0 balance1 reserve0 reserve1).accountMap := by
    simpa [uniswapUpdateCumulativePackedMapWith, uniswapUpdateCumulativePackedWordWith,
      syncUpdateCumulativePackedReserveStateWith, syncUpdatePackedReserveState, evmP0,
      evmP1, σP1, packedCumulative, storageStore_executionEnv, henv, henvP0] using
      hPackedAccounts
  have hReturnAccounts :=
    accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨1⟩ hPackedAccountsCumulative
  simpa [uniswapUpdateCumulativeReturnMapWith, uniswapLockExitedState, uniswapUnlockedState,
    storageStore_accountMap, storageStore_executionEnv,
    syncUpdateCumulativePackedReserveStateWith, henv] using hReturnAccounts
/-
  let reserve0Word : UInt256 := uniswapUpdateReserve0Word σ I
  let reserve1Word : UInt256 := uniswapUpdateReserve1Word σ I
  let elapsedWord : UInt256 := uniswapUpdateElapsedFromStorage σ I
  let price0Word : UInt256 :=
    uniswapUpdatePrice0CumulativeWord σ I elapsedWord reserve1Word reserve0Word
  let σP0 : AccountMap := sstoreAccountMap I.codeOwner σ ⟨9⟩ price0Word
  have helapsedSource :
      elapsedWord = uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σ I) I := by
    simp [elapsedWord, uniswapUpdateElapsedFromStorage, uniswapUpdateElapsedWord,
      uniswapUpdateTimestampWord, uniswapSlotWord]
  let evmP0 :=
    Solm.EVM.storageStore evm I.codeOwner ⟨9⟩
      (EVM.wordOfInt (syncPrice0CumulativeIntAt evm evm))
  have hprice0Nat :
      syncPrice0CumulativeIntAt evm evm =
        Int.ofNat ((uniswapSlotWord ⟨9⟩ σ I).toNat +
          (reserve1Word.toNat * 2 ^ 112 / reserve0Word.toNat) *
            (UInt256.land reserve32Mask elapsedWord).toNat) %
          twoPow256 := by
    exact syncPrice0CumulativeIntAt_eq_updateWord_nat_form
      (σStorage := σ) (σUpdate := σ)
      (storageEvm := evm) (updateEvm := evm)
      (I := I) (elapsed := elapsedWord)
      (reserve1 := reserve1Word) (reserve0 := reserve0Word)
      hAccounts henv henv hslot8 helapsedSource
      (by rfl) (by rfl)
  have hprice0Eq :
      EVM.wordOfInt (syncPrice0CumulativeIntAt evm evm) = price0Word := by
    let n : Nat := (uniswapSlotWord ⟨9⟩ σ I).toNat +
      (reserve1Word.toNat * 2 ^ 112 / reserve0Word.toNat) *
        (UInt256.land reserve32Mask elapsedWord).toNat
    have hn : syncPrice0CumulativeIntAt evm evm = Int.ofNat n % twoPow256 := by
      simpa [n] using hprice0Nat
    rw [hn, wordOfInt_nat_mod_twoPow256 n]
    apply u256_inj
    rw [uniswapUpdatePrice0CumulativeWord_toNat]
    · change (Fin.ofNat UInt256.size n).val = n % UInt256.size
      simp [Fin.ofNat]
    · dsimp [reserve1Word, uniswapUpdateReserve1Word]
      exact uniswapUint112Masked_lt _
    · dsimp [reserve0Word, uniswapUpdateReserve0Word]
      exact uniswapUint112Masked_lt _
  have hP0Accounts : accountMapEquiv σP0 evmP0.accountMap := by
    have hs := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨9⟩ price0Word hAccounts
    simpa [σP0, evmP0, storageStore_accountMap, hprice0Eq] using hs
  have henvP0 : evmP0.executionEnv = I := by
    simp [evmP0, storageStore_executionEnv, henv]
  let price1Word : UInt256 :=
    uniswapUpdatePrice1CumulativeWord σP0 I elapsedWord reserve0Word reserve1Word
  let σP1 : AccountMap := sstoreAccountMap I.codeOwner σP0 ⟨10⟩ price1Word
  let evmP1 :=
    Solm.EVM.storageStore evmP0 I.codeOwner ⟨10⟩
      (EVM.wordOfInt (syncPrice1CumulativeIntAt evmP0 evm))
  have hprice1Nat :
      syncPrice1CumulativeIntAt evmP0 evm =
        Int.ofNat ((uniswapSlotWord ⟨10⟩ σP0 I).toNat +
          (reserve0Word.toNat * 2 ^ 112 / reserve1Word.toNat) *
            (UInt256.land elapsedWord reserve32Mask).toNat) %
          twoPow256 := by
    exact syncPrice1CumulativeIntAt_eq_updateWord_nat_form
      (σStorage := σP0) (σUpdate := σ)
      (storageEvm := evmP0) (updateEvm := evm)
      (I := I) (elapsed := elapsedWord)
      (reserve0 := reserve0Word) (reserve1 := reserve1Word)
      hP0Accounts henvP0 henv hslot8 helapsedSource
      (by rfl) (by rfl)
  have hprice1Eq :
      EVM.wordOfInt (syncPrice1CumulativeIntAt evmP0 evm) = price1Word := by
    let n : Nat := (uniswapSlotWord ⟨10⟩ σP0 I).toNat +
      (reserve0Word.toNat * 2 ^ 112 / reserve1Word.toNat) *
        (UInt256.land elapsedWord reserve32Mask).toNat
    have hn : syncPrice1CumulativeIntAt evmP0 evm = Int.ofNat n % twoPow256 := by
      simpa [n] using hprice1Nat
    rw [hn, wordOfInt_nat_mod_twoPow256 n]
    apply u256_inj
    rw [uniswapUpdatePrice1CumulativeWord_toNat]
    · change (Fin.ofNat UInt256.size n).val = n % UInt256.size
      simp [Fin.ofNat]
    · dsimp [reserve0Word, uniswapUpdateReserve0Word]
      exact uniswapUint112Masked_lt _
    · dsimp [reserve1Word, uniswapUpdateReserve1Word]
      exact uniswapUint112Masked_lt _
  have hP1Accounts : accountMapEquiv σP1 evmP1.accountMap := by
    have hs := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨10⟩ price1Word hP0Accounts
    simpa [σP1, evmP1, storageStore_accountMap, hprice1Eq] using hs
  have henvP1 : evmP1.executionEnv = I := by
    simp [evmP1, storageStore_executionEnv, henvP0]
  have hslot8P1 :
      Solm.EVM.storageLoad evmP1 evmP1.executionEnv.codeOwner ⟨8⟩ =
        uniswapSlotWord ⟨8⟩ σP1 I := by
    have h := accountMapEquiv_storage_findD hP1Accounts I.codeOwner ⟨8⟩ ⟨0⟩
    simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
      uniswapSlotWord, henvP1] at h ⊢
    exact h.symm
  let packedCumulative : UInt256 := uniswapUpdateCumulativePackedWord σ I balance0 balance1
  have hPackedAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σP1 ⟨8⟩ packedCumulative)
        (syncUpdatePackedReserveState evmP1 balance0 balance1).accountMap :=
    accountMapEquiv_syncUpdatePackedReserveState hP1Accounts henvP1 hslot8P1 (by rfl)
  have hPackedAccountsCumulative :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σP1 ⟨8⟩ packedCumulative)
        (syncUpdateCumulativePackedReserveState evm balance0 balance1).accountMap := by
    simpa [syncUpdateCumulativePackedReserveState, syncUpdatePackedReserveState, evmP0,
      evmP1, storageStore_executionEnv, henv, henvP0] using hPackedAccounts
  have hReturnAccounts :=
    accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨1⟩ hPackedAccountsCumulative
  simpa [uniswapUpdateCumulativeReturnMap, uniswapUpdateCumulativePackedMap,
    uniswapUpdateCumulativePackedWord, uniswapUpdatePrice1CumulativeMap,
    uniswapUpdatePrice0CumulativeMap, reserve0Word, reserve1Word, elapsedWord,
    price0Word, price1Word, σP0, σP1, packedCumulative, uniswapLockExitedState,
    uniswapUnlockedState, storageStore_accountMap, storageStore_executionEnv,
    syncUpdateCumulativePackedReserveState, henv] using hReturnAccounts
-/

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000000 in
theorem uniswapSyncBodyCumulativeSuccess
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cA'' : Batteries.RBSet AccountAddress compare} {σ'' : AccountMap}
    {o o1 : ByteArray} {evm1S : EVM.State} {balance0 balance1 : UInt256}
    {k7060 C7060 : ℕ}
    (hcode : I.code = uniswapV2PairBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some syncTransition)
    (hsz4 : 4 ≤ I.calldata.size)
    (hperm : I.perm = true)
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ syncTransition.body
        (.returned (syncAfterUpdateFrame balance0 balance1)
          (uniswapLockExitedState
            (syncUpdateCumulativePackedReserveState evm1S balance0 balance1))
          none))
    (hPostAccounts1 : accountMapEquiv σ'' evm1S.accountMap)
    (hcreated1 : evm1S.createdAccounts = cA'')
    (henv1I : evm1S.executionEnv = I)
    (hslotWordSource :
      Solm.EVM.storageLoad evm1S evm1S.executionEnv.codeOwner ⟨8⟩ =
        uniswapSlotWord ⟨8⟩ σ'' I)
    (rd7060 :
      RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨7060⟩
        [ UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σ'' I) reserve112Shift)
            reserve112Mask,
          UInt256.land (uniswapSlotWord ⟨8⟩ σ'' I) reserve112Mask,
          balance1, balance0, ⟨6363⟩, ⟨570⟩, uniswapSelWord I ]
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        (UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat 128 36)
          128 32))
        o1 (cA'', σ'') k7060 C7060)
    (hmemSize :
      (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1).size =
        164)
    (hmemRead64 :
      (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1).readWithPadding
          64 32 =
        UInt256.toByteArray ⟨128⟩)
    (ho32 : 32 ≤ o.size)
    (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size)
    (ho1Size : o1.size < UInt256.size)
    (helapsedNe :
      UInt256.land (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σ'' I) I)
          reserve32Mask ≠
        ⟨0⟩)
    (hreserve0Nonzero :
      UInt256.land (uniswapSlotWord ⟨8⟩ σ'' I) reserve112Mask ≠ ⟨0⟩)
    (hreserve1Nonzero :
      UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σ'' I) reserve112Shift)
          reserve112Mask ≠
        ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hmemSize128 :
      128 ≤ (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1).size := by
    rw [hmemSize]
    omega
  have rd7060' :
      RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨7060⟩
        [uniswapUpdateReserve1Word σ'' I, uniswapUpdateReserve0Word σ'' I,
          balance1, balance0, ⟨6363⟩, ⟨570⟩, uniswapSelWord I]
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        balanceOfThisStaticcallActiveWords o1 (cA'', σ'') k7060 C7060 := by
    simpa [uniswapUpdateReserve0Word, uniswapUpdateReserve1Word,
      balanceOfThisStaticcallActiveWords] using rd7060
  have rdRet :=
    RD.uniswapUpdateCumulativesToReturn rd7060' hmemSize128 hmemRead64
      ho32 hoSize ho132 ho1Size
      (by
        simpa [uniswapUpdateElapsedWord, uniswapUpdateTimestampWord, uniswapSlotWord]
          using helapsedNe)
      (by simpa [uniswapUpdateReserve0Word] using hreserve0Nonzero)
      (by simpa [uniswapUpdateReserve1Word] using hreserve1Nonzero)
      hperm
  have hCreatedRet :
      cA'' =
        (uniswapLockExitedState
          (syncUpdateCumulativePackedReserveState evm1S balance0 balance1)).createdAccounts := by
    simp [uniswapLockExitedState, uniswapUnlockedState, syncUpdateCumulativePackedReserveState,
      storageStore_createdAccounts, hcreated1]
  have hAccountsRet :=
    accountMapEquiv_syncUpdateCumulativeReturnMap
      (balance0 := balance0) (balance1 := balance1)
      hPostAccounts1 henv1I hslotWordSource
  exact rdRet.reEquivExecutionGenAccountMapEquiv hcode hdispatch
    (uniswapDecode_sync hsz4) hbody hCreatedRet hAccountsRet
    (returnEquiv.fallthrough rfl rfl (by decide +native))
/-
  let mem0 := balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1
  have hmemSize128 : 128 ≤ mem0.size := by
    change 128 ≤ (balanceOfThisRebuiltStaticcallMem
      (UInt256.ofNat I.codeOwner.val) o o1).size
    rw [hmemSize]
    omega
  have hmemRead64Local :
      mem0.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [mem0] using hmemRead64
  let reserve0Word : UInt256 := UInt256.land (uniswapSlotWord ⟨8⟩ σ'' I) reserve112Mask
  let reserve1Word : UInt256 :=
    UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σ'' I) reserve112Shift) reserve112Mask
  let elapsedWord : UInt256 := uniswapUpdateElapsedFromStorage σ'' I
  let timestampWord : UInt256 := uniswapUpdateTimestampWord I
  let price0Word : UInt256 :=
    uniswapUpdatePrice0CumulativeWord σ'' I elapsedWord reserve1Word reserve0Word
  let σP0 : AccountMap := sstoreAccountMap I.codeOwner σ'' ⟨9⟩ price0Word
  let price1Word : UInt256 :=
    uniswapUpdatePrice1CumulativeWord σP0 I elapsedWord reserve0Word reserve1Word
  let σP1 : AccountMap := sstoreAccountMap I.codeOwner σP0 ⟨10⟩ price1Word
  let packedCumulative : UInt256 :=
    uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σP1 I) timestampWord balance1 balance0
  have helapsedSource :
      elapsedWord = uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σ'' I) I := by
    simp [elapsedWord, uniswapUpdateElapsedFromStorage, uniswapUpdateElapsedWord,
      uniswapUpdateTimestampWord, uniswapSlotWord]
  have hreserve0Masked : UInt256.land reserve0Word reserve112Mask = reserve0Word := by
    dsimp [reserve0Word]
    exact uint112Mask_idempotent (uniswapSlotWord ⟨8⟩ σ'' I)
  have hreserve1Masked : UInt256.land reserve1Word reserve112Mask = reserve1Word := by
    dsimp [reserve1Word]
    exact uint112Mask_idempotent
      (UInt256.div (uniswapSlotWord ⟨8⟩ σ'' I) reserve112Shift)
  have hreserve0Ne : UInt256.land reserve0Word reserve112Mask ≠ ⟨0⟩ := by
    rw [hreserve0Masked]
    simpa [reserve0Word] using hreserve0Nonzero
  have hreserve1Ne : UInt256.land reserve1Word reserve112Mask ≠ ⟨0⟩ := by
    rw [hreserve1Masked]
    simpa [reserve1Word] using hreserve1Nonzero
  obtain ⟨_, _, rd7241⟩ :=
    RD.uniswapUpdateCumulativesAndJump rd7060
      (by
        simpa [uniswapUpdateElapsedFromStorage, uniswapUpdateElapsedWord,
          uniswapUpdateTimestampWord, uniswapSlotWord] using helapsedNe)
      (by simpa [reserve0Word, reserve1Word] using hreserve0Ne)
      (by simpa [reserve0Word, reserve1Word] using hreserve1Ne)
      hperm
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd7339⟩ :=
    RD.uniswapUpdateStorePackedReserves
      (by
        simpa [elapsedWord, timestampWord, price0Word, σP0, price1Word, σP1,
          reserve0Word, reserve1Word, mem0, uniswapUpdateElapsedFromStorage,
          uniswapUpdateElapsedWord, uniswapUpdateTimestampWord, uniswapSlotWord] using rd7241)
      hperm
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd6363⟩ :=
    RD.uniswapUpdateEmitSyncAndJump
      (packed := packedCumulative) (ret := ⟨6363⟩)
      (R := [⟨570⟩, uniswapSelWord I])
      (mem := mem0) (aw := balanceOfThisStaticcallActiveWords)
      (awLoad := balanceOfThisStaticcallActiveWords)
      (awLog := balanceOfThisStaticcallActiveWords)
      (mcostLoad := 0) (mcostStore0 := 0) (mcostStore1 := 0)
      (mcostLoadLog := 0) (mcostLog := 0)
      (by
        simpa [packedCumulative, elapsedWord, timestampWord, price0Word, σP0,
          price1Word, σP1, reserve0Word, reserve1Word, mem0, uniswapUpdateElapsedFromStorage,
          uniswapUpdateElapsedWord, uniswapUpdateTimestampWord, uniswapSlotWord] using rd7339)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
        decide +native)
      (by
        simpa [mem0] using
          balanceOfThisRebuiltStaticcallMem_mload64_of_size_ge
            (UInt256.ofNat I.codeOwner.val) o o1 ho32 hoSize ho132 ho1Size)
      (by decide +native)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
        decide +native)
      (by decide +native)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
        decide +native)
      (by decide +native)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
        decide +native)
      (by
        simpa [mem0] using
          uniswapSyncLogMem_mload64 packedCumulative mem0 hmemSize128 hmemRead64Local)
      (by decide +native)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
        decide +native)
      (by decide +native) hperm (by jump_dest)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have rdRet := RD.uniswapSyncAfterUpdateToReturn rd6363 hperm
  let evmP0 :=
    Solm.EVM.storageStore evm1S I.codeOwner ⟨9⟩
      (EVM.wordOfInt (syncPrice0CumulativeIntAt evm1S evm1S))
  have hprice0Nat :
      syncPrice0CumulativeIntAt evm1S evm1S =
        Int.ofNat ((uniswapSlotWord ⟨9⟩ σ'' I).toNat +
          (reserve1Word.toNat * 2 ^ 112 / reserve0Word.toNat) *
            (UInt256.land reserve32Mask elapsedWord).toNat) %
          twoPow256 := by
    exact syncPrice0CumulativeIntAt_eq_updateWord_nat_form
      (σStorage := σ'') (σUpdate := σ'')
      (storageEvm := evm1S) (updateEvm := evm1S)
      (I := I) (elapsed := elapsedWord)
      (reserve1 := reserve1Word) (reserve0 := reserve0Word)
      hPostAccounts1 henv1I henv1I hslotWordSource helapsedSource (by rfl) (by rfl)
  have hprice0Eq :
      EVM.wordOfInt (syncPrice0CumulativeIntAt evm1S evm1S) = price0Word := by
    let n : Nat := (uniswapSlotWord ⟨9⟩ σ'' I).toNat +
      (reserve1Word.toNat * 2 ^ 112 / reserve0Word.toNat) *
        (UInt256.land reserve32Mask elapsedWord).toNat
    have hn :
        syncPrice0CumulativeIntAt evm1S evm1S = Int.ofNat n % twoPow256 := by
      simpa [n] using hprice0Nat
    rw [hn, wordOfInt_nat_mod_twoPow256 n]
    apply u256_inj
    rw [uniswapUpdatePrice0CumulativeWord_toNat]
    · change (Fin.ofNat UInt256.size n).val = n % UInt256.size
      simp [Fin.ofNat]
    · dsimp [reserve1Word]
      exact uniswapUint112Masked_lt _
    · dsimp [reserve0Word]
      exact uniswapUint112Masked_lt _
  have hP0Accounts : accountMapEquiv σP0 evmP0.accountMap := by
    have hs := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨9⟩ price0Word hPostAccounts1
    simpa [σP0, evmP0, storageStore_accountMap, hprice0Eq] using hs
  have henvP0 : evmP0.executionEnv = I := by
    simp [evmP0, storageStore_executionEnv, henv1I]
  let evmP1 :=
    Solm.EVM.storageStore evmP0 I.codeOwner ⟨10⟩
      (EVM.wordOfInt (syncPrice1CumulativeIntAt evmP0 evm1S))
  have hprice1Nat :
      syncPrice1CumulativeIntAt evmP0 evm1S =
        Int.ofNat ((uniswapSlotWord ⟨10⟩ σP0 I).toNat +
          (reserve0Word.toNat * 2 ^ 112 / reserve1Word.toNat) *
            (UInt256.land elapsedWord reserve32Mask).toNat) %
          twoPow256 := by
    exact syncPrice1CumulativeIntAt_eq_updateWord_nat_form
      (σStorage := σP0) (σUpdate := σ'')
      (storageEvm := evmP0) (updateEvm := evm1S)
      (I := I) (elapsed := elapsedWord)
      (reserve0 := reserve0Word) (reserve1 := reserve1Word)
      hP0Accounts henvP0 henv1I hslotWordSource helapsedSource (by rfl) (by rfl)
  have hprice1Eq :
      EVM.wordOfInt (syncPrice1CumulativeIntAt evmP0 evm1S) = price1Word := by
    let n : Nat := (uniswapSlotWord ⟨10⟩ σP0 I).toNat +
      (reserve0Word.toNat * 2 ^ 112 / reserve1Word.toNat) *
        (UInt256.land elapsedWord reserve32Mask).toNat
    have hn :
        syncPrice1CumulativeIntAt evmP0 evm1S = Int.ofNat n % twoPow256 := by
      simpa [n] using hprice1Nat
    rw [hn, wordOfInt_nat_mod_twoPow256 n]
    apply u256_inj
    rw [uniswapUpdatePrice1CumulativeWord_toNat]
    · change (Fin.ofNat UInt256.size n).val = n % UInt256.size
      simp [Fin.ofNat]
    · dsimp [reserve0Word]
      exact uniswapUint112Masked_lt _
    · dsimp [reserve1Word]
      exact uniswapUint112Masked_lt _
  have hP1Accounts : accountMapEquiv σP1 evmP1.accountMap := by
    have hs := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨10⟩ price1Word hP0Accounts
    simpa [σP1, evmP1, storageStore_accountMap, hprice1Eq] using hs
  have henvP1 : evmP1.executionEnv = I := by
    simp [evmP1, storageStore_executionEnv, henvP0]
  have hslot8P1 :
      Solm.EVM.storageLoad evmP1 evmP1.executionEnv.codeOwner ⟨8⟩ =
        uniswapSlotWord ⟨8⟩ σP1 I := by
    have h := accountMapEquiv_storage_findD hP1Accounts I.codeOwner ⟨8⟩ ⟨0⟩
    simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
      uniswapSlotWord, henvP1] at h ⊢
    exact h.symm
  have hPackedAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σP1 ⟨8⟩ packedCumulative)
        (syncUpdatePackedReserveState evmP1 balance0 balance1).accountMap :=
    accountMapEquiv_syncUpdatePackedReserveState hP1Accounts henvP1 hslot8P1 (by rfl)
  have hPackedAccountsCumulative :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σP1 ⟨8⟩ packedCumulative)
        (syncUpdateCumulativePackedReserveState evm1S balance0 balance1).accountMap := by
    simpa [syncUpdateCumulativePackedReserveState, syncUpdatePackedReserveState, evmP0,
      evmP1, storageStore_executionEnv, henv1I, henvP0] using hPackedAccounts
  have hCreatedRet :
      cA'' =
        (uniswapLockExitedState
          (syncUpdateCumulativePackedReserveState evm1S balance0 balance1)).createdAccounts := by
    simp [uniswapLockExitedState, uniswapUnlockedState, syncUpdateCumulativePackedReserveState,
      storageStore_createdAccounts, hcreated1]
  have hAccountsRet :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σP1 ⟨8⟩ packedCumulative) ⟨12⟩ ⟨1⟩)
        (uniswapLockExitedState
          (syncUpdateCumulativePackedReserveState evm1S balance0 balance1)).accountMap := by
    have hs :=
      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨1⟩ hPackedAccountsCumulative
    simpa [uniswapLockExitedState, uniswapUnlockedState, storageStore_accountMap,
      storageStore_executionEnv, syncUpdateCumulativePackedReserveState, henv1I] using hs
  exact rdRet.reEquivExecutionGenAccountMapEquiv hcode hdispatch
    (uniswapDecode_sync hsz4) hbody hCreatedRet hAccountsRet
    (returnEquiv.fallthrough rfl rfl (by decide +native))
-/

end UniswapV2Pair
