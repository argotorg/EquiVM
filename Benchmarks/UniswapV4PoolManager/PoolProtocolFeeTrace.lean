import Benchmarks.UniswapV4PoolManager.PoolProtocolFeeSource
import Benchmarks.UniswapV4PoolManager.PoolCheckTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_013

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

open poolManagerBlocks in
theorem poolProtocolFeeStaticTrace {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length+9 ≤ 1024) (hperm : ee.perm = false)
    (h : RD (immutableLayout.runtime poolManagerBytecode immWords) ee g s0 ⟨3855⟩
      (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C) :
    RDstatic (immutableLayout.runtime poolManagerBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨3855⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨3856⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨3857⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 411376114810372856684520561905785191840737028508569010899517440) (width := 26) (op := .PUSH26) (by decide) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨3858⟩ : UInt256), UInt8.ofNat 121, .Push .PUSH26, some ((UInt256.ofNat 411376114810372856684520561905785191840737028508569010899517440), 26), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup4 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨3885⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 184) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨3886⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 184), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.shl (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨3888⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.and (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨3889⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.swap1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨3890⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.pushConst (UInt256.ofNat 115792089237315784047456174635831223332708078880448723302429075438902230122495) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨3891⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237315784047456174635831223332708078880448723302429075438902230122495), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.and (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨3924⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.or (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨3925⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.swap1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨3926⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.sstoreStatic r13 hperm (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨3927⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

theorem protocolFeeShiftMaskClean (fee : UInt256) (hc : fee.toNat < 2^24) :
    UInt256.land (UInt256.shiftLeft fee (UInt256.ofNat 184))
      (UInt256.ofNat 411376114810372856684520561905785191840737028508569010899517440) =
      UInt256.shiftLeft fee ⟨184⟩ := by
  rw [u256_land_comm]
  exact shiftedMaskClean _ _ (n := 184) (bits := 24) (by decide) hc
    (by change fee.toNat * 2^184 < 2^256; omega) (by native_decide)

theorem poolProtocolFeeStoreTrace {I : ExecutionEnv} {g : Sat256} {s0 : State} {evm : EVM.State}
    {mem rdata : ByteArray} {aw id fee x2 x3 x4 : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+9 ≤ 1024) (hI : evm.executionEnv = I)
    (hc : fee.toNat < 2^24)
    (h : RD (deployedRuntime v) I g s0 ⟨3855⟩ (poolSlot id :: fee :: x2 :: x3 :: x4 :: R)
      mem aw rdata evm.accountMap k C) :
    if I.perm = false then RDstatic (deployedRuntime v) g s0 else
      RDret (deployedRuntime v) g s0 (poolSetProtocolPost evm id fee).accountMap .empty := by
  by_cases hp : I.perm = false
  · rw [if_pos hp]
    exact poolProtocolFeeStaticTrace hstack hp h
  · rw [if_neg hp]
    have hr := poolManagerBlocks.poolManager_block_3855 hstack (Bool.eq_true_of_not_eq_false hp) h
    have hword : solcSlotWordAt (poolSlot id) evm.accountMap I = poolSlot0Word evm id :=
      (storageLoad_codeOwner_eq_solcSlotWordAt evm I _ (by rw [hI])).symm
    change RDret _ _ _ (sstoreAccountMap I.codeOwner evm.accountMap (poolSlot id)
      (UInt256.lor (UInt256.land protocolFeeClearMask (solcSlotWordAt (poolSlot id) evm.accountMap I))
        (UInt256.land (UInt256.shiftLeft fee (UInt256.ofNat 184))
          (UInt256.ofNat 411376114810372856684520561905785191840737028508569010899517440)))) .empty at hr
    rw [protocolFeeShiftMaskClean fee hc, hword, u256_land_comm protocolFeeClearMask] at hr
    have hm : (poolSetProtocolPost evm id fee).accountMap =
        sstoreAccountMap I.codeOwner evm.accountMap (poolSlot id)
          (slot0ProtocolFeeWord (poolSlot0Word evm id) fee) := by
      rw [poolSetProtocolPost, storageStore_accountMap, hI]
    rw [hm]
    exact hr

@[irreducible] def poolSetProtocolTraceResult (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256)
    (s0 : State) (evm : EVM.State) (id fee : UInt256) : Prop :=
  if poolSqrtPriceWord evm id = ⟨0⟩ then RDrev (deployedRuntime v) g s0 else
  if I.perm = false then RDstatic (deployedRuntime v) g s0 else
    RDret (deployedRuntime v) g s0 (poolSetProtocolPost evm id fee).accountMap .empty

theorem poolProtocolFeeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State} {evm : EVM.State}
    {mem rdata : ByteArray} {aw id fee x2 x3 x4 : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+9 ≤ 1024) (hI : evm.executionEnv = I)
    (hc : fee.toNat < 2^24)
    (h : RD (deployedRuntime v) I g s0 ⟨13686⟩
      (poolSlot id :: ⟨3855⟩ :: poolSlot id :: fee :: x2 :: x3 :: x4 :: R) mem aw rdata evm.accountMap k C) :
    poolSetProtocolTraceResult v I g s0 evm id fee := by
  have hword : slot0SqrtPriceWord (solcSlotWordAt (poolSlot id) evm.accountMap I) = poolSqrtPriceWord evm id := by
    unfold poolSqrtPriceWord poolSlot0Word
    rw [storageLoad_codeOwner_eq_solcSlotWordAt evm I _ (by rw [hI])]
  have hcheck := poolCheckTrace v (by simp; omega)
    (by rw [deployedRuntime_jumps]; jump_dest) h
  rw [hword] at hcheck
  unfold poolSetProtocolTraceResult
  rcases hcheck with ⟨hz, hr⟩ | ⟨hz, k1, C1, hstore⟩
  · rw [if_pos hz]; exact hr
  · rw [if_neg hz]
    exact poolProtocolFeeStoreTrace v hstack hI hc hstore

end Benchmarks.UniswapV4PoolManager
