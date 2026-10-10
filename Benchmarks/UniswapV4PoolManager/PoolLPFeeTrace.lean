import Benchmarks.UniswapV4PoolManager.PoolLPFeeSource
import Benchmarks.UniswapV4PoolManager.PoolCheckTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_025

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

open poolManagerBlocks in
theorem poolLPFeeStaticTrace {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = false)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 8656) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RDstatic (immutableLayout.runtime poolManagerBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8656⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8657⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8658⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 115792082335570260009146527875442584318540171552157837553037437240354742992895) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8659⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792082335570260009146527875442584318540171552157837553037437240354742992895), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.and (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8692⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 208) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8693⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 208), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8695⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.swap1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8696⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.swap2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8697⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.shl (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8698⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.pushConst (UInt256.ofNat 6901745935414424457133245323534729813113482726486420146767558386647040) (width := 29) (op := .PUSH29) (by decide) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8699⟩ : UInt256), UInt8.ofNat 124, .Push .PUSH29, some ((UInt256.ofNat 6901745935414424457133245323534729813113482726486420146767558386647040), 29), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.and (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8729⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.or (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8730⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.swap1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8731⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.sstoreStatic r14 hperm (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8732⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

theorem lpFeeShiftMaskClean (fee : UInt256) (hc : fee.toNat < 2^24) :
    UInt256.land (UInt256.ofNat 6901745935414424457133245323534729813113482726486420146767558386647040)
      (UInt256.shiftLeft fee (UInt256.ofNat 208)) = UInt256.shiftLeft fee ⟨208⟩ := by
  exact shiftedMaskClean _ _ (n := 208) (bits := 24) (by decide) hc
    (by change fee.toNat * 2^208 < 2^256; omega) (by native_decide)

theorem poolLPFeeStoreTrace {I : ExecutionEnv} {g : Sat256} {s0 : State} {evm : EVM.State}
    {mem rdata : ByteArray} {aw id fee : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+4 ≤ 1024) (hI : evm.executionEnv = I)
    (hc : fee.toNat < 2^24)
    (h : RD (deployedRuntime v) I g s0 ⟨8656⟩ (fee :: poolSlot id :: R) mem aw rdata evm.accountMap k C) :
    if I.perm = false then RDstatic (deployedRuntime v) g s0 else
      RDret (deployedRuntime v) g s0 (poolSetFeePost evm id fee).accountMap .empty := by
  by_cases hp : I.perm = false
  · rw [if_pos hp]
    exact poolLPFeeStaticTrace hstack hp h
  · rw [if_neg hp]
    have hr := poolManagerBlocks.poolManager_block_8656 hstack (Bool.eq_true_of_not_eq_false hp) h
    have hword : solcSlotWordAt (poolSlot id) evm.accountMap I = poolSlot0Word evm id :=
      (storageLoad_codeOwner_eq_solcSlotWordAt evm I _ (by rw [hI])).symm
    change RDret _ _ _ (sstoreAccountMap I.codeOwner evm.accountMap (poolSlot id)
      (UInt256.lor (UInt256.land (UInt256.ofNat 6901745935414424457133245323534729813113482726486420146767558386647040)
        (UInt256.shiftLeft fee (UInt256.ofNat 208))) (UInt256.land lpFeeClearMask
          (solcSlotWordAt (poolSlot id) evm.accountMap I)))) .empty at hr
    rw [lpFeeShiftMaskClean fee hc, hword, u256_land_comm lpFeeClearMask, u256_lor_comm] at hr
    have hm : (poolSetFeePost evm id fee).accountMap =
        sstoreAccountMap I.codeOwner evm.accountMap (poolSlot id) (slot0LPFeeWord (poolSlot0Word evm id) fee) := by
      rw [poolSetFeePost, storageStore_accountMap, hI]
    rw [hm]
    exact hr

@[irreducible] def poolSetFeeTraceResult (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256)
    (s0 : State) (evm : EVM.State) (id fee : UInt256) : Prop :=
  if poolSqrtPriceWord evm id = ⟨0⟩ then RDrev (deployedRuntime v) g s0 else
  if I.perm = false then RDstatic (deployedRuntime v) g s0 else
    RDret (deployedRuntime v) g s0 (poolSetFeePost evm id fee).accountMap .empty

theorem poolLPFeeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State} {evm : EVM.State}
    {mem rdata : ByteArray} {aw id fee : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+5 ≤ 1024) (hI : evm.executionEnv = I)
    (hc : fee.toNat < 2^24)
    (h : RD (deployedRuntime v) I g s0 ⟨13686⟩
      (poolSlot id :: ⟨8656⟩ :: fee :: poolSlot id :: R) mem aw rdata evm.accountMap k C) :
    poolSetFeeTraceResult v I g s0 evm id fee := by
  have hword : slot0SqrtPriceWord (solcSlotWordAt (poolSlot id) evm.accountMap I) = poolSqrtPriceWord evm id := by
    unfold poolSqrtPriceWord poolSlot0Word
    rw [storageLoad_codeOwner_eq_solcSlotWordAt evm I _ (by rw [hI])]
  have hcheck := poolCheckTrace v (by simp; omega)
    (by rw [deployedRuntime_jumps]; jump_dest) h
  rw [hword] at hcheck
  unfold poolSetFeeTraceResult
  rcases hcheck with ⟨hz, hr⟩ | ⟨hz, k1, C1, hstore⟩
  · rw [if_pos hz]; exact hr
  · rw [if_neg hz]
    exact poolLPFeeStoreTrace v (by omega) hI hc hstore

end Benchmarks.UniswapV4PoolManager
