import Benchmarks.UniswapV3Pool.BurnPositionUpdatePostReturn

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

private theorem uniswapV3PoolBurnPositionUpdateTokensOwedStoreDecodeEqTemplate
    {v : PoolImmutables} {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlo : 21807 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21986) :
    decode code pc = decode uniswapV3PoolBytecode pc := by
  exact uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch
    (by
      have hsize : 21986 ≤ uniswapV3PoolBytecode.size := by native_decide
      omega)
    (by
      intro p hp
      simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord,
        List.lookup] at hp
      rcases hp with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals omega)

theorem uniswapV3PoolBurnPositionUpdateTokensOwed1NonzeroStore {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {tokensOwed1 tokensOwed0 liquidity freePtr inside1 inside0 delta posBase retPos
      inside1' inside0' z2 z3 fee1 fee0 posBase' tick delta' upper lower owner ret
      free : UInt256}
    {R : List UInt256} {mem : ByteArray} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hperm : ee.perm = true)
    (h : RD code ee g s0 ⟨21861⟩
      (tokensOwed1 :: tokensOwed0 :: liquidity :: freePtr :: inside1 :: inside0 ::
        delta :: posBase :: retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 ::
        fee0 :: posBase' :: tick :: delta' :: upper :: lower :: owner :: ret ::
        free :: R)
      mem aw rdata (cA, σ) k C)
    (htokens0 : UInt256.land burnPositionUpdateSlot0Mask tokensOwed0 = ⟨0⟩)
    (htokens1 : UInt256.land burnPositionUpdateSlot0Mask tokensOwed1 ≠ ⟨0⟩)
    (hov : R.length + 35 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21954⟩
      (tokensOwed1 :: tokensOwed0 :: liquidity :: freePtr :: inside1 :: inside0 ::
        delta :: posBase :: retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 ::
        fee0 :: posBase' :: tick :: delta' :: upper :: lower :: owner :: ret ::
        free :: R)
      mem aw rdata
      (cA, sstoreAccountMap ee.codeOwner σ (posBase + (⟨3⟩ : UInt256))
        (burnPositionUpdateTokensOwedAddedSlot3
          (solcSlotWord σ ee (posBase + (⟨3⟩ : UInt256))) tokensOwed0 tokensOwed1))
      k' C' := by
  have hdec (pc : UInt256)
      (hlo : 21807 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21930) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnPositionUpdateTokensOwedStoreDecodeEqTemplate hpatch hlo
      (by omega)
  have hd21861 :
      decode code ⟨21861⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨21861⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21863 :
      decode code ⟨21863⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨21863⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21865 :
      decode code ⟨21865⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdec ⟨21865⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21867 : decode code ⟨21867⟩ = some (.SHL, .none) := by
    rw [hdec ⟨21867⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21868 : decode code ⟨21868⟩ = some (.SUB, .none) := by
    rw [hdec ⟨21868⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21869 : decode code ⟨21869⟩ = some (.DUP3, .none) := by
    rw [hdec ⟨21869⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21870 : decode code ⟨21870⟩ = some (.AND, .none) := by
    rw [hdec ⟨21870⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21871 : decode code ⟨21871⟩ = some (.ISZERO, .none) := by
    rw [hdec ⟨21871⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21872 : decode code ⟨21872⟩ = some (.ISZERO, .none) := by
    rw [hdec ⟨21872⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21873 : decode code ⟨21873⟩ = some (.DUP1, .none) := by
    rw [hdec ⟨21873⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21874 :
      decode code ⟨21874⟩ = some (.Push .PUSH2, some (⟨21892⟩, 2)) := by
    rw [hdec ⟨21874⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21877 : decode code ⟨21877⟩ = some (.JUMPI, .none) := by
    rw [hdec ⟨21877⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21878 : decode code ⟨21878⟩ = some (.POP, .none) := by
    rw [hdec ⟨21878⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21879 :
      decode code ⟨21879⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdec ⟨21879⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21881 : decode code ⟨21881⟩ = some (.DUP2, .none) := by
    rw [hdec ⟨21881⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21882 :
      decode code ⟨21882⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨21882⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21884 :
      decode code ⟨21884⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨21884⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21886 :
      decode code ⟨21886⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdec ⟨21886⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21888 : decode code ⟨21888⟩ = some (.SHL, .none) := by
    rw [hdec ⟨21888⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21889 : decode code ⟨21889⟩ = some (.SUB, .none) := by
    rw [hdec ⟨21889⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21890 : decode code ⟨21890⟩ = some (.AND, .none) := by
    rw [hdec ⟨21890⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21891 : decode code ⟨21891⟩ = some (.GT, .none) := by
    rw [hdec ⟨21891⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21892 : decode code ⟨21892⟩ = some (.JUMPDEST, .none) := by
    rw [hdec ⟨21892⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21893 : decode code ⟨21893⟩ = some (.ISZERO, .none) := by
    rw [hdec ⟨21893⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21894 :
      decode code ⟨21894⟩ = some (.Push .PUSH2, some (⟨21954⟩, 2)) := by
    rw [hdec ⟨21894⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21897 : decode code ⟨21897⟩ = some (.JUMPI, .none) := by
    rw [hdec ⟨21897⟩ (by native_decide) (by native_decide)]
    native_decide
  have rd21877 := evm_run h with [
    raw push1 ⟨1⟩ hd21861 (by evm_ov),
    raw push1 ⟨1⟩ hd21863 (by evm_ov),
    raw push1 ⟨128⟩ hd21865 (by evm_ov),
    raw shl hd21867 (by evm_ov),
    raw sub hd21868 (by evm_ov),
    raw dup3 hd21869 (by simp only [List.length_cons] at hov ⊢; omega),
    raw and hd21870 (by evm_ov),
    raw iszero hd21871 (by evm_ov),
    raw iszero hd21872 (by evm_ov),
    raw dup1 hd21873 (by simp only [List.length_cons] at hov ⊢; omega),
    raw push2 ⟨21892⟩ hd21874 (by evm_ov)]
  have hcond0 :
      UInt256.isZero
          (UInt256.isZero (UInt256.land tokensOwed0 burnPositionUpdateSlot0Mask)) =
        ⟨0⟩ := by
    rw [u256_land_comm tokensOwed0 burnPositionUpdateSlot0Mask]
    rw [htokens0]
    native_decide
  have rd21878 := by
    simpa [burnPositionUpdateSlot0Mask] using
      rd21877.jumpiNT hd21877 hcond0
        (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21892 := evm_run rd21878 with [
    raw pop hd21878 (by simp only [List.length_cons] at hov ⊢; omega),
    raw push1 ⟨0⟩ hd21879 (by evm_ov),
    raw dup2 hd21881 (by simp only [List.length_cons] at hov ⊢; omega),
    raw push1 ⟨1⟩ hd21882 (by evm_ov),
    raw push1 ⟨1⟩ hd21884 (by evm_ov),
    raw push1 ⟨128⟩ hd21886 (by evm_ov),
    raw shl hd21888 (by evm_ov),
    raw sub hd21889 (by evm_ov),
    raw and hd21890 (by evm_ov),
    raw gt hd21891 (by evm_ov),
    raw jumpdest hd21892 (by evm_ov),
    raw iszero hd21893 (by evm_ov),
    raw push2 ⟨21954⟩ hd21894 (by evm_ov)]
  have hgt1 :
      UInt256.gt (UInt256.land burnPositionUpdateSlot0Mask tokensOwed1) ⟨0⟩ = ⟨1⟩ := by
    apply ugt_one
    have hpos : 0 < (UInt256.land burnPositionUpdateSlot0Mask tokensOwed1).toNat := by
      apply Nat.pos_of_ne_zero
      intro hz
      exact htokens1 (uint256_toNat_eq_zero hz)
    simpa using hpos
  have hcond1 :
      UInt256.isZero
          (UInt256.gt (UInt256.land burnPositionUpdateSlot0Mask tokensOwed1) ⟨0⟩) =
        ⟨0⟩ := by
    rw [hgt1]
    native_decide
  have rd21898 := rd21892.jumpiNT hd21897 hcond1
    (by simp only [List.length_cons] at hov ⊢; omega)
  exact uniswapV3PoolBurnPositionUpdateStoreTokensOwedSlot3
    (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
    (tokensOwed1 := tokensOwed1) (tokensOwed0 := tokensOwed0)
    (liquidity := liquidity) (freePtr := freePtr) (inside1 := inside1)
    (inside0 := inside0) (delta := delta) (posBase := posBase) (retPos := retPos)
    (inside1' := inside1') (inside0' := inside0') (z2 := z2) (z3 := z3)
    (fee1 := fee1) (fee0 := fee0) (posBase' := posBase') (tick := tick)
    (delta' := delta') (upper := upper) (lower := lower) (owner := owner)
    (ret := ret) (free := free) (R := R) (mem := mem) (aw := aw)
    (rdata := rdata) (cA := cA) (σ := σ) hpatch hperm rd21898 hov

private theorem uniswapV3PoolBurnModifyPositionReturnToCallerDecodeEqTemplateGeneric
    {v : PoolImmutables} {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlo : 16428 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 16841) :
    decode code pc = decode uniswapV3PoolBytecode pc := by
  exact uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch
    (by
      have hsize : 16841 ≤ uniswapV3PoolBytecode.size := by native_decide
      omega)
    (by
      intro p hp
      simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord,
        List.lookup] at hp
      rcases hp with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals omega)

theorem uniswapV3PoolBurnModifyPositionReturnZeroAmountToCallerGeneric
    {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {posBase free r1 r2 r3 ret : UInt256}
    {R : List UInt256} {mem : ByteArray} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hdest : (D_J code 0).contains ret = true)
    (hzero : burnAmountCleanWord ee = ⟨0⟩)
    (hmload224 :
      (if (⟨224⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨224⟩ : UInt256) ≥ UInt256.ofNat 22 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨224⟩ : UInt256).toNat 32))) =
        UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)))
    (h : RD code ee g s0 ⟨16428⟩
      (posBase :: free :: r1 :: r2 :: r3 :: ⟨128⟩ :: ret :: R)
      mem (UInt256.ofNat 22) rdata acc k C)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret (r1 :: r2 :: posBase :: R)
      mem (UInt256.ofNat 22) rdata acc k' C' := by
  have hdec (pc : UInt256)
      (hlo : 16428 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 16841) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnModifyPositionReturnToCallerDecodeEqTemplateGeneric hpatch hlo hhi
  have hd16428 : decode code ⟨16428⟩ = some (.JUMPDEST, .none) := by
    rw [hdec ⟨16428⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16429 : decode code ⟨16429⟩ = some (.SWAP4, .none) := by
    rw [hdec ⟨16429⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16430 : decode code ⟨16430⟩ = some (.POP, .none) := by
    rw [hdec ⟨16430⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16431 : decode code ⟨16431⟩ = some (.DUP5, .none) := by
    rw [hdec ⟨16431⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16432 :
      decode code ⟨16432⟩ = some (.Push .PUSH1, some (⟨96⟩, 1)) := by
    rw [hdec ⟨16432⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16434 : decode code ⟨16434⟩ = some (.ADD, .none) := by
    rw [hdec ⟨16434⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16435 : decode code ⟨16435⟩ = some (.MLOAD, .none) := by
    rw [hdec ⟨16435⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16436 :
      decode code ⟨16436⟩ = some (.Push .PUSH1, some (⟨15⟩, 1)) := by
    rw [hdec ⟨16436⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16438 : decode code ⟨16438⟩ = some (.SIGNEXTEND, .none) := by
    rw [hdec ⟨16438⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16439 :
      decode code ⟨16439⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdec ⟨16439⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16441 : decode code ⟨16441⟩ = some (.EQ, .none) := by
    rw [hdec ⟨16441⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16442 :
      decode code ⟨16442⟩ = some (.Push .PUSH2, some (⟨16801⟩, 2)) := by
    rw [hdec ⟨16442⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16445 : decode code ⟨16445⟩ = some (.JUMPI, .none) := by
    rw [hdec ⟨16445⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16801 : decode code ⟨16801⟩ = some (.JUMPDEST, .none) := by
    rw [hdec ⟨16801⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16802 : decode code ⟨16802⟩ = some (.POP, .none) := by
    rw [hdec ⟨16802⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16803 : decode code ⟨16803⟩ = some (.SWAP2, .none) := by
    rw [hdec ⟨16803⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16804 : decode code ⟨16804⟩ = some (.SWAP4, .none) := by
    rw [hdec ⟨16804⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16805 : decode code ⟨16805⟩ = some (.SWAP1, .none) := by
    rw [hdec ⟨16805⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16806 : decode code ⟨16806⟩ = some (.SWAP3, .none) := by
    rw [hdec ⟨16806⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16807 : decode code ⟨16807⟩ = some (.POP, .none) := by
    rw [hdec ⟨16807⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16808 : decode code ⟨16808⟩ = some (.JUMP, .none) := by
    rw [hdec ⟨16808⟩ (by native_decide) (by native_decide)]
    native_decide
  have rd16435 := evm_run h with [
    raw jumpdest hd16428 (by evm_ov),
    raw swap4 hd16429 (by simp only [List.length_cons] at hov ⊢; omega),
    raw pop hd16430 (by simp only [List.length_cons] at hov ⊢; omega),
    raw dup5 hd16431 (by simp only [List.length_cons] at hov ⊢; omega),
    raw push1 ⟨96⟩ hd16432 (by evm_ov),
    raw add hd16434 (by evm_ov)]
  have rd16436 := by
    simpa [show ((⟨128⟩ : UInt256) + ⟨96⟩) = (⟨224⟩ : UInt256) from by decide,
      show ((⟨96⟩ : UInt256) + ⟨128⟩) = (⟨224⟩ : UInt256) from by decide] using
      rd16435.mload 0
        (UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)))
        (UInt256.ofNat 22) hd16435 mem_cost hmload224
        (by native_decide)
        (by simp only [List.length_cons] at hov ⊢; omega)
  have rd16438 := evm_run rd16436 with [
    raw push1 ⟨15⟩ hd16436 (by evm_ov)]
  have rd16439 := by
    simpa using burnRDSignextend rd16438 hd16438
      (by simp only [List.length_cons] at hov ⊢; omega)
  have rd16445 := evm_run rd16439 with [
    raw push1 ⟨0⟩ hd16439 (by evm_ov),
    raw eq hd16441 (by evm_ov),
    raw push2 ⟨16801⟩ hd16442 (by evm_ov)]
  have hcond :
      UInt256.eq ⟨0⟩
          (UInt256.signextend ⟨15⟩
            (UInt256.signextend ⟨15⟩
              (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)))) ≠
        ⟨0⟩ := by
    rw [hzero]
    native_decide
  have rd16801 := rd16445.jumpiT hd16445 hcond
    (uniswapV3PoolJumpDestPatched16801 hpatch)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd16808 := evm_run rd16801 with [
    raw jumpdest hd16801 (by evm_ov),
    raw pop hd16802 (by simp only [List.length_cons] at hov ⊢; omega),
    raw swap2 hd16803 (by simp only [List.length_cons] at hov ⊢; omega),
    raw swap4 hd16804 (by omega),
    raw swap1 hd16805 (by simp only [List.length_cons]; omega),
    raw swap3 hd16806 (by simp only [List.length_cons]; omega),
    raw pop hd16807 (by simp only [List.length_cons]; omega)]
  exact ⟨_, _, rd16808.jump hd16808 hdest
    (by simp only [List.length_cons]; omega)⟩

theorem uniswapV3PoolBurnPositionUpdateTokensOwed0NonzeroZeroDeltaReturnToCaller
    {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {tokensOwed1 tokensOwed0 liquidity inside1 inside0 delta posBase inside1' inside0'
      z2 z3 fee1 fee0 posBase' tick delta' upper lower owner free r1 r2 r3 callerRet :
      UInt256}
    {R : List UInt256} {mem : ByteArray} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hdest : (D_J code 0).contains callerRet = true)
    (hperm : ee.perm = true)
    (hzero : burnAmountCleanWord ee = ⟨0⟩)
    (hmload224 :
      (if (⟨224⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨224⟩ : UInt256) ≥ UInt256.ofNat 22 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨224⟩ : UInt256).toNat 32))) =
        UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)))
    (h : RD code ee g s0 ⟨21861⟩
      (tokensOwed1 :: tokensOwed0 :: liquidity :: burnPositionKeyNewFreePtrWord ::
        inside1 :: inside0 :: delta :: posBase :: ⟨19527⟩ :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower ::
        owner :: ⟨16428⟩ :: free :: r1 :: r2 :: r3 :: ⟨128⟩ :: callerRet :: R)
      mem (UInt256.ofNat 22) rdata (cA, σ) k C)
    (htokens0 : UInt256.land burnPositionUpdateSlot0Mask tokensOwed0 ≠ ⟨0⟩)
    (hdelta : UInt256.slt (UInt256.signextend ⟨15⟩ delta') ⟨0⟩ = ⟨0⟩)
    (hov : R.length + 40 ≤ 1024) :
    ∃ k' C', RD code ee g s0 callerRet (r1 :: r2 :: posBase' :: R)
      mem (UInt256.ofNat 22) rdata
      (cA, sstoreAccountMap ee.codeOwner σ (posBase + (⟨3⟩ : UInt256))
        (burnPositionUpdateTokensOwedAddedSlot3
          (solcSlotWord σ ee (posBase + (⟨3⟩ : UInt256))) tokensOwed0 tokensOwed1))
      k' C' := by
  obtain ⟨_, _, hrd21954⟩ :=
    uniswapV3PoolBurnPositionUpdateTokensOwed0NonzeroStore
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (tokensOwed1 := tokensOwed1) (tokensOwed0 := tokensOwed0)
      (liquidity := liquidity) (freePtr := burnPositionKeyNewFreePtrWord)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩) (inside1' := inside1')
      (inside0' := inside0') (z2 := z2) (z3 := z3) (fee1 := fee1)
      (fee0 := fee0) (posBase' := posBase') (tick := tick)
      (delta' := delta') (upper := upper) (lower := lower) (owner := owner)
      (ret := ⟨16428⟩) (free := free)
      (R := r1 :: r2 :: r3 :: ⟨128⟩ :: callerRet :: R) (mem := mem)
      (aw := UInt256.ofNat 22) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hperm h htokens0
      (by simp only [List.length_cons] at hov ⊢; omega)
  obtain ⟨_, _, hrd19527⟩ :=
    uniswapV3PoolBurnPositionUpdatePostReturnJump
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (tokensOwed1 := tokensOwed1) (tokensOwed0 := tokensOwed0)
      (liquidity := liquidity) (freePtr := burnPositionKeyNewFreePtrWord)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩) (inside1' := inside1')
      (inside0' := inside0') (z2 := z2) (z3 := z3) (fee1 := fee1)
      (fee0 := fee0) (posBase' := posBase') (tick := tick)
      (delta' := delta') (upper := upper) (lower := lower) (owner := owner)
      (ret := ⟨16428⟩) (free := free)
      (R := r1 :: r2 :: r3 :: ⟨128⟩ :: callerRet :: R) (mem := mem)
      (aw := UInt256.ofNat 22) (rdata := rdata)
      (acc := (cA, sstoreAccountMap ee.codeOwner σ (posBase + (⟨3⟩ : UInt256))
        (burnPositionUpdateTokensOwedAddedSlot3
          (solcSlotWord σ ee (posBase + (⟨3⟩ : UInt256))) tokensOwed0 tokensOwed1)))
      hpatch (uniswapV3PoolJumpDestPatched19527 hpatch) hrd21954
      (by simp only [List.length_cons] at hov ⊢; omega)
  obtain ⟨_, _, hrd16428⟩ :=
    uniswapV3PoolBurnModifyPositionAfterPositionUpdateZeroDeltaReturn
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1') (inside0 := inside0') (z2 := z2) (z3 := z3)
      (fee1 := fee1) (fee0 := fee0) (posBase := posBase') (tick := tick)
      (delta := delta') (upper := upper) (lower := lower) (owner := owner)
      (ret := ⟨16428⟩) (free := free)
      (R := r1 :: r2 :: r3 :: ⟨128⟩ :: callerRet :: R) (mem := mem)
      (aw := UInt256.ofNat 22) (rdata := rdata)
      (acc := (cA, sstoreAccountMap ee.codeOwner σ (posBase + (⟨3⟩ : UInt256))
        (burnPositionUpdateTokensOwedAddedSlot3
          (solcSlotWord σ ee (posBase + (⟨3⟩ : UInt256))) tokensOwed0 tokensOwed1)))
      hpatch (uniswapV3PoolJumpDestPatched16428 hpatch) hrd19527 hdelta
      (by simp only [List.length_cons] at hov ⊢; omega)
  exact uniswapV3PoolBurnModifyPositionReturnZeroAmountToCallerGeneric
    (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
    (posBase := posBase') (free := free) (r1 := r1) (r2 := r2) (r3 := r3)
    (ret := callerRet) (R := R) (mem := mem) (rdata := rdata)
    (acc := (cA, sstoreAccountMap ee.codeOwner σ (posBase + (⟨3⟩ : UInt256))
      (burnPositionUpdateTokensOwedAddedSlot3
        (solcSlotWord σ ee (posBase + (⟨3⟩ : UInt256))) tokensOwed0 tokensOwed1)))
    hpatch hdest hzero hmload224 hrd16428
    (by omega)

theorem uniswapV3PoolBurnPositionUpdateTokensOwed1NonzeroZeroDeltaReturnToCaller
    {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {tokensOwed1 tokensOwed0 liquidity inside1 inside0 delta posBase inside1' inside0'
      z2 z3 fee1 fee0 posBase' tick delta' upper lower owner free r1 r2 r3 callerRet :
      UInt256}
    {R : List UInt256} {mem : ByteArray} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hdest : (D_J code 0).contains callerRet = true)
    (hperm : ee.perm = true)
    (hzero : burnAmountCleanWord ee = ⟨0⟩)
    (hmload224 :
      (if (⟨224⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨224⟩ : UInt256) ≥ UInt256.ofNat 22 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨224⟩ : UInt256).toNat 32))) =
        UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)))
    (h : RD code ee g s0 ⟨21861⟩
      (tokensOwed1 :: tokensOwed0 :: liquidity :: burnPositionKeyNewFreePtrWord ::
        inside1 :: inside0 :: delta :: posBase :: ⟨19527⟩ :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower ::
        owner :: ⟨16428⟩ :: free :: r1 :: r2 :: r3 :: ⟨128⟩ :: callerRet :: R)
      mem (UInt256.ofNat 22) rdata (cA, σ) k C)
    (htokens0 : UInt256.land burnPositionUpdateSlot0Mask tokensOwed0 = ⟨0⟩)
    (htokens1 : UInt256.land burnPositionUpdateSlot0Mask tokensOwed1 ≠ ⟨0⟩)
    (hdelta : UInt256.slt (UInt256.signextend ⟨15⟩ delta') ⟨0⟩ = ⟨0⟩)
    (hov : R.length + 40 ≤ 1024) :
    ∃ k' C', RD code ee g s0 callerRet (r1 :: r2 :: posBase' :: R)
      mem (UInt256.ofNat 22) rdata
      (cA, sstoreAccountMap ee.codeOwner σ (posBase + (⟨3⟩ : UInt256))
        (burnPositionUpdateTokensOwedAddedSlot3
          (solcSlotWord σ ee (posBase + (⟨3⟩ : UInt256))) tokensOwed0 tokensOwed1))
      k' C' := by
  obtain ⟨_, _, hrd21954⟩ :=
    uniswapV3PoolBurnPositionUpdateTokensOwed1NonzeroStore
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (tokensOwed1 := tokensOwed1) (tokensOwed0 := tokensOwed0)
      (liquidity := liquidity) (freePtr := burnPositionKeyNewFreePtrWord)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩) (inside1' := inside1')
      (inside0' := inside0') (z2 := z2) (z3 := z3) (fee1 := fee1)
      (fee0 := fee0) (posBase' := posBase') (tick := tick)
      (delta' := delta') (upper := upper) (lower := lower) (owner := owner)
      (ret := ⟨16428⟩) (free := free)
      (R := r1 :: r2 :: r3 :: ⟨128⟩ :: callerRet :: R) (mem := mem)
      (aw := UInt256.ofNat 22) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hperm h htokens0 htokens1
      (by simp only [List.length_cons] at hov ⊢; omega)
  obtain ⟨_, _, hrd19527⟩ :=
    uniswapV3PoolBurnPositionUpdatePostReturnJump
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (tokensOwed1 := tokensOwed1) (tokensOwed0 := tokensOwed0)
      (liquidity := liquidity) (freePtr := burnPositionKeyNewFreePtrWord)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩) (inside1' := inside1')
      (inside0' := inside0') (z2 := z2) (z3 := z3) (fee1 := fee1)
      (fee0 := fee0) (posBase' := posBase') (tick := tick)
      (delta' := delta') (upper := upper) (lower := lower) (owner := owner)
      (ret := ⟨16428⟩) (free := free)
      (R := r1 :: r2 :: r3 :: ⟨128⟩ :: callerRet :: R) (mem := mem)
      (aw := UInt256.ofNat 22) (rdata := rdata)
      (acc := (cA, sstoreAccountMap ee.codeOwner σ (posBase + (⟨3⟩ : UInt256))
        (burnPositionUpdateTokensOwedAddedSlot3
          (solcSlotWord σ ee (posBase + (⟨3⟩ : UInt256))) tokensOwed0 tokensOwed1)))
      hpatch (uniswapV3PoolJumpDestPatched19527 hpatch) hrd21954
      (by simp only [List.length_cons] at hov ⊢; omega)
  obtain ⟨_, _, hrd16428⟩ :=
    uniswapV3PoolBurnModifyPositionAfterPositionUpdateZeroDeltaReturn
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1') (inside0 := inside0') (z2 := z2) (z3 := z3)
      (fee1 := fee1) (fee0 := fee0) (posBase := posBase') (tick := tick)
      (delta := delta') (upper := upper) (lower := lower) (owner := owner)
      (ret := ⟨16428⟩) (free := free)
      (R := r1 :: r2 :: r3 :: ⟨128⟩ :: callerRet :: R) (mem := mem)
      (aw := UInt256.ofNat 22) (rdata := rdata)
      (acc := (cA, sstoreAccountMap ee.codeOwner σ (posBase + (⟨3⟩ : UInt256))
        (burnPositionUpdateTokensOwedAddedSlot3
          (solcSlotWord σ ee (posBase + (⟨3⟩ : UInt256))) tokensOwed0 tokensOwed1)))
      hpatch (uniswapV3PoolJumpDestPatched16428 hpatch) hrd19527 hdelta
      (by simp only [List.length_cons] at hov ⊢; omega)
  exact uniswapV3PoolBurnModifyPositionReturnZeroAmountToCallerGeneric
    (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
    (posBase := posBase') (free := free) (r1 := r1) (r2 := r2) (r3 := r3)
    (ret := callerRet) (R := R) (mem := mem) (rdata := rdata)
    (acc := (cA, sstoreAccountMap ee.codeOwner σ (posBase + (⟨3⟩ : UInt256))
      (burnPositionUpdateTokensOwedAddedSlot3
        (solcSlotWord σ ee (posBase + (⟨3⟩ : UInt256))) tokensOwed0 tokensOwed1)))
    hpatch hdest hzero hmload224 hrd16428
    (by omega)

theorem uniswapV3PoolBurnPositionUpdateTokensOwedZeroSkipStoresGeneric
    {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {tokensOwed1 tokensOwed0 liquidity inside1 inside0 delta posBase retPos inside1'
      inside0' z2 z3 fee1 fee0 posBase' tick delta' upper lower owner ret free :
      UInt256}
    {R : List UInt256} {mem : ByteArray} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨21861⟩
      (tokensOwed1 :: tokensOwed0 :: liquidity :: burnPositionKeyNewFreePtrWord ::
        inside1 :: inside0 :: delta :: posBase :: retPos :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower ::
        owner :: ret :: free :: R)
      mem (UInt256.ofNat 22) rdata acc k C)
    (htokens0 : UInt256.land burnPositionUpdateSlot0Mask tokensOwed0 = ⟨0⟩)
    (htokens1 : UInt256.land burnPositionUpdateSlot0Mask tokensOwed1 = ⟨0⟩)
    (hov : R.length + 35 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21954⟩
      (tokensOwed1 :: tokensOwed0 :: liquidity :: burnPositionKeyNewFreePtrWord ::
        inside1 :: inside0 :: delta :: posBase :: retPos :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower ::
        owner :: ret :: free :: R)
      mem (UInt256.ofNat 22) rdata acc k' C' := by
  have hdec (pc : UInt256)
      (hlo : 21807 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21930) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnPositionUpdateTokensOwedStoreDecodeEqTemplate hpatch hlo
      (by omega)
  have hd21861 :
      decode code ⟨21861⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨21861⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21863 :
      decode code ⟨21863⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨21863⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21865 :
      decode code ⟨21865⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdec ⟨21865⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21867 : decode code ⟨21867⟩ = some (.SHL, .none) := by
    rw [hdec ⟨21867⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21868 : decode code ⟨21868⟩ = some (.SUB, .none) := by
    rw [hdec ⟨21868⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21869 : decode code ⟨21869⟩ = some (.DUP3, .none) := by
    rw [hdec ⟨21869⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21870 : decode code ⟨21870⟩ = some (.AND, .none) := by
    rw [hdec ⟨21870⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21871 : decode code ⟨21871⟩ = some (.ISZERO, .none) := by
    rw [hdec ⟨21871⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21872 : decode code ⟨21872⟩ = some (.ISZERO, .none) := by
    rw [hdec ⟨21872⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21873 : decode code ⟨21873⟩ = some (.DUP1, .none) := by
    rw [hdec ⟨21873⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21874 :
      decode code ⟨21874⟩ = some (.Push .PUSH2, some (⟨21892⟩, 2)) := by
    rw [hdec ⟨21874⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21877 : decode code ⟨21877⟩ = some (.JUMPI, .none) := by
    rw [hdec ⟨21877⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21878 : decode code ⟨21878⟩ = some (.POP, .none) := by
    rw [hdec ⟨21878⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21879 :
      decode code ⟨21879⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdec ⟨21879⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21881 : decode code ⟨21881⟩ = some (.DUP2, .none) := by
    rw [hdec ⟨21881⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21882 :
      decode code ⟨21882⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨21882⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21884 :
      decode code ⟨21884⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨21884⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21886 :
      decode code ⟨21886⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdec ⟨21886⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21888 : decode code ⟨21888⟩ = some (.SHL, .none) := by
    rw [hdec ⟨21888⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21889 : decode code ⟨21889⟩ = some (.SUB, .none) := by
    rw [hdec ⟨21889⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21890 : decode code ⟨21890⟩ = some (.AND, .none) := by
    rw [hdec ⟨21890⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21891 : decode code ⟨21891⟩ = some (.GT, .none) := by
    rw [hdec ⟨21891⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21892 : decode code ⟨21892⟩ = some (.JUMPDEST, .none) := by
    rw [hdec ⟨21892⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21893 : decode code ⟨21893⟩ = some (.ISZERO, .none) := by
    rw [hdec ⟨21893⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21894 :
      decode code ⟨21894⟩ = some (.Push .PUSH2, some (⟨21954⟩, 2)) := by
    rw [hdec ⟨21894⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21897 : decode code ⟨21897⟩ = some (.JUMPI, .none) := by
    rw [hdec ⟨21897⟩ (by native_decide) (by native_decide)]
    native_decide
  have rd21877 := evm_run h with [
    raw push1 ⟨1⟩ hd21861 (by evm_ov),
    raw push1 ⟨1⟩ hd21863 (by evm_ov),
    raw push1 ⟨128⟩ hd21865 (by evm_ov),
    raw shl hd21867 (by evm_ov),
    raw sub hd21868 (by evm_ov),
    raw dup3 hd21869 (by simp only [List.length_cons] at hov ⊢; omega),
    raw and hd21870 (by evm_ov),
    raw iszero hd21871 (by evm_ov),
    raw iszero hd21872 (by evm_ov),
    raw dup1 hd21873 (by simp only [List.length_cons] at hov ⊢; omega),
    raw push2 ⟨21892⟩ hd21874 (by evm_ov)]
  have hcond0 :
      UInt256.isZero
          (UInt256.isZero (UInt256.land tokensOwed0 burnPositionUpdateSlot0Mask)) =
        ⟨0⟩ := by
    rw [u256_land_comm tokensOwed0 burnPositionUpdateSlot0Mask]
    rw [htokens0]
    native_decide
  have rd21878 := by
    simpa [burnPositionUpdateSlot0Mask] using
      rd21877.jumpiNT hd21877 hcond0
        (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21892 := evm_run rd21878 with [
    raw pop hd21878 (by simp only [List.length_cons] at hov ⊢; omega),
    raw push1 ⟨0⟩ hd21879 (by evm_ov),
    raw dup2 hd21881 (by simp only [List.length_cons] at hov ⊢; omega),
    raw push1 ⟨1⟩ hd21882 (by evm_ov),
    raw push1 ⟨1⟩ hd21884 (by evm_ov),
    raw push1 ⟨128⟩ hd21886 (by evm_ov),
    raw shl hd21888 (by evm_ov),
    raw sub hd21889 (by evm_ov),
    raw and hd21890 (by evm_ov),
    raw gt hd21891 (by evm_ov),
    raw jumpdest hd21892 (by evm_ov),
    raw iszero hd21893 (by evm_ov),
    raw push2 ⟨21954⟩ hd21894 (by evm_ov)]
  have hcond1 :
      UInt256.isZero
          (UInt256.gt (UInt256.land burnPositionUpdateSlot0Mask tokensOwed1) ⟨0⟩) ≠
        ⟨0⟩ := by
    rw [htokens1]
    native_decide
  exact ⟨_, _, by
    simpa [burnPositionUpdateSlot0Mask] using
      rd21892.jumpiT hd21897 hcond1 (uniswapV3PoolJumpDestPatched21954 hpatch)
        (by simp only [List.length_cons] at hov ⊢; omega)⟩

theorem uniswapV3PoolBurnPositionUpdateTokensOwedZeroZeroDeltaReturnToCallerGeneric
    {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {tokensOwed1 tokensOwed0 liquidity inside1 inside0 delta posBase inside1' inside0'
      z2 z3 fee1 fee0 posBase' tick delta' upper lower owner free r1 r2 r3 callerRet :
      UInt256}
    {R : List UInt256} {mem : ByteArray} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hdest : (D_J code 0).contains callerRet = true)
    (hzero : burnAmountCleanWord ee = ⟨0⟩)
    (hmload224 :
      (if (⟨224⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨224⟩ : UInt256) ≥ UInt256.ofNat 22 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨224⟩ : UInt256).toNat 32))) =
        UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)))
    (h : RD code ee g s0 ⟨21861⟩
      (tokensOwed1 :: tokensOwed0 :: liquidity :: burnPositionKeyNewFreePtrWord ::
        inside1 :: inside0 :: delta :: posBase :: ⟨19527⟩ :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower ::
        owner :: ⟨16428⟩ :: free :: r1 :: r2 :: r3 :: ⟨128⟩ :: callerRet :: R)
      mem (UInt256.ofNat 22) rdata acc k C)
    (htokens0 : UInt256.land burnPositionUpdateSlot0Mask tokensOwed0 = ⟨0⟩)
    (htokens1 : UInt256.land burnPositionUpdateSlot0Mask tokensOwed1 = ⟨0⟩)
    (hdelta : UInt256.slt (UInt256.signextend ⟨15⟩ delta') ⟨0⟩ = ⟨0⟩)
    (hov : R.length + 40 ≤ 1024) :
    ∃ k' C', RD code ee g s0 callerRet (r1 :: r2 :: posBase' :: R)
      mem (UInt256.ofNat 22) rdata acc k' C' := by
  obtain ⟨_, _, hrd21954⟩ :=
    uniswapV3PoolBurnPositionUpdateTokensOwedZeroSkipStoresGeneric
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (tokensOwed1 := tokensOwed1) (tokensOwed0 := tokensOwed0)
      (liquidity := liquidity) (inside1 := inside1) (inside0 := inside0)
      (delta := delta) (posBase := posBase) (retPos := ⟨19527⟩)
      (inside1' := inside1') (inside0' := inside0') (z2 := z2) (z3 := z3)
      (fee1 := fee1) (fee0 := fee0) (posBase' := posBase') (tick := tick)
      (delta' := delta') (upper := upper) (lower := lower) (owner := owner)
      (ret := ⟨16428⟩) (free := free)
      (R := r1 :: r2 :: r3 :: ⟨128⟩ :: callerRet :: R) (mem := mem)
      (rdata := rdata) (acc := acc) hpatch h htokens0 htokens1
      (by simp only [List.length_cons] at hov ⊢; omega)
  obtain ⟨_, _, hrd19527⟩ :=
    uniswapV3PoolBurnPositionUpdatePostReturnJump
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (tokensOwed1 := tokensOwed1) (tokensOwed0 := tokensOwed0)
      (liquidity := liquidity) (freePtr := burnPositionKeyNewFreePtrWord)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩) (inside1' := inside1')
      (inside0' := inside0') (z2 := z2) (z3 := z3) (fee1 := fee1)
      (fee0 := fee0) (posBase' := posBase') (tick := tick)
      (delta' := delta') (upper := upper) (lower := lower) (owner := owner)
      (ret := ⟨16428⟩) (free := free)
      (R := r1 :: r2 :: r3 :: ⟨128⟩ :: callerRet :: R) (mem := mem)
      (aw := UInt256.ofNat 22) (rdata := rdata) (acc := acc)
      hpatch (uniswapV3PoolJumpDestPatched19527 hpatch) hrd21954
      (by simp only [List.length_cons] at hov ⊢; omega)
  obtain ⟨_, _, hrd16428⟩ :=
    uniswapV3PoolBurnModifyPositionAfterPositionUpdateZeroDeltaReturn
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1') (inside0 := inside0') (z2 := z2) (z3 := z3)
      (fee1 := fee1) (fee0 := fee0) (posBase := posBase') (tick := tick)
      (delta := delta') (upper := upper) (lower := lower) (owner := owner)
      (ret := ⟨16428⟩) (free := free)
      (R := r1 :: r2 :: r3 :: ⟨128⟩ :: callerRet :: R) (mem := mem)
      (aw := UInt256.ofNat 22) (rdata := rdata) (acc := acc)
      hpatch (uniswapV3PoolJumpDestPatched16428 hpatch) hrd19527 hdelta
      (by simp only [List.length_cons] at hov ⊢; omega)
  exact uniswapV3PoolBurnModifyPositionReturnZeroAmountToCallerGeneric
    (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
    (posBase := posBase') (free := free) (r1 := r1) (r2 := r2) (r3 := r3)
    (ret := callerRet) (R := R) (mem := mem) (rdata := rdata) (acc := acc)
    hpatch hdest hzero hmload224 hrd16428
    (by omega)

end Benchmarks.UniswapV3Pool
