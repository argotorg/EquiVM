import Benchmarks.UniswapV3.Pool.ObserveInputMemory
import Benchmarks.UniswapV3.Pool.Slot0Memory
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_030
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_031

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem observeInputWordArithmetic (n : Nat) (hn : n ≤ 2 ^ 32) :
    (UInt256.mul (UInt256.ofNat 32) (UInt256.ofNat n)).toNat = 32 * n ∧
    UInt256.ofNat 128 + (UInt256.ofNat 32 + UInt256.mul (UInt256.ofNat 32) (UInt256.ofNat n)) =
      observeInputFree n ∧
    (UInt256.ofNat 160 + UInt256.mul (UInt256.ofNat 32) (UInt256.ofNat n)).toNat = 160 + 32 * n := by
  have hm : (UInt256.mul (UInt256.ofNat 32) (UInt256.ofNat n)).toNat = 32 * n := by
    rw [u256_mul_toNat, ulit_toNat' n (by change _ < 2 ^ 256; omega)]
    change (32 * n) % UInt256.size = _
    exact Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega)
  have ha : (UInt256.ofNat 32 + UInt256.mul (UInt256.ofNat 32) (UInt256.ofNat n)).toNat =
      32 + 32 * n := by
    rw [uadd_toNat, hm]
    change (32 + 32 * n) % UInt256.size = 32 + 32 * n
    exact Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega)
  refine ⟨hm, ?_, ?_⟩
  · apply u256_inj
    rw [uadd_toNat, ha, observeInputFree, ulit_toNat' (160 + 32 * n)
      (by change _ < 2 ^ 256; omega)]
    change (128 + (32 + 32 * n)) % UInt256.size = _
    rw [Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega)]
    omega
  · rw [uadd_toNat, hm]
    change (160 + 32 * n) % UInt256.size = 160 + 32 * n
    exact Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega)

theorem observeInputExpansion (n : Nat) (hn : n ≤ 2 ^ 32) :
    M (M ⟨5⟩ (UInt256.ofNat 160) (UInt256.mul (UInt256.ofNat 32) (UInt256.ofNat n)))
      (UInt256.ofNat 160 + UInt256.mul (UInt256.ofNat 32) (UInt256.ofNat n)) ⟨32⟩ =
      observeInputAw n := by
  obtain ⟨hm, _, he⟩ := observeInputWordArithmetic n hn
  have hinner : M ⟨5⟩ (UInt256.ofNat 160)
      (UInt256.mul (UInt256.ofNat 32) (UInt256.ofNat n)) = UInt256.ofNat (n + 5) := by
    change UInt256.ofNat (MachineState.M 5 160 _) = _
    rw [hm]
    congr 1
    unfold MachineState.M
    split <;> omega
  rw [hinner]
  change UInt256.ofNat (MachineState.M (UInt256.ofNat (n + 5)).toNat _ 32) = _
  rw [he, ulit_toNat' (n + 5) (by change _ < 2 ^ 256; omega)]
  unfold observeInputAw
  congr 1
  unfold MachineState.M
  change max (n + 5) ((160 + 32 * n + 32 + 31) / 32) = n + 6
  omega

theorem observeInputMem_eq (I : ExecutionEnv) (start n : Nat)
    (hn : n ≤ 2 ^ 32) (hstart : start < UInt256.size) :
    uniswapV3Pool_block_9458_memory (ee := I) (mem := solcFreePtrMem)
      (x4 := UInt256.ofNat n) (x5 := UInt256.ofNat start) = observeInputMem I.calldata start n := by
  have hload : memLoad (UInt256.ofNat 64) solcFreePtrMem = UInt256.ofNat 128 :=
    mloadWordValue_of_readWithPadding (by rw [solcFreePtrMem_size]; decide) solcFreePtrMem_read64
  obtain ⟨hm, hf, he⟩ := observeInputWordArithmetic n hn
  simp only [uniswapV3Pool_block_9458_memory, hload, hm, hf, ulit_toNat' start hstart]
  change writeWord (I.calldata.write start
    (writeWord (writeWord solcFreePtrMem 64 (observeInputFree n)) 128 (UInt256.ofNat n))
    160 (32 * n)) (UInt256.ofNat 160 + UInt256.mul (UInt256.ofNat 32) (UInt256.ofNat n)).toNat
    (UInt256.ofNat 0) = _
  rw [he]
  rfl

theorem observeStorageArgs (σ : AccountMap) (I : ExecutionEnv) :
    UInt256.land (UInt256.div (solcSlotWordAt ⟨0⟩ σ I)
      (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 200))) (UInt256.ofNat 65535) =
      slot0FieldWord 25 2 σ I ∧
    UInt256.land (solcSlotWordAt ⟨4⟩ σ I)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) =
      poolLiquidityWord σ I := by
  have hs : UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 200) =
      UInt256.ofNat (256 ^ 25) := by native_decide
  have hm : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 128 - 1) := by native_decide
  rw [hs, hm]
  exact ⟨rfl, rfl⟩

theorem observeInputX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {rdata : ByteArray} {k C n start : Nat} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨9458⟩
      (UInt256.ofNat ee.header.timestamp :: ⟨9566⟩ :: ⟨96⟩ :: ⟨96⟩ ::
        UInt256.ofNat n :: UInt256.ofNat start :: R) solcFreePtrMem ⟨3⟩ rdata σ k C)
    (hn : n ≤ 2 ^ 32) (hstart : start < UInt256.size) (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨16967⟩
      (slot0FieldWord 25 2 σ ee :: poolLiquidityWord σ ee :: slot0FieldWord 23 2 σ ee ::
        EVM.wordOfInt (slot0TickValue σ ee) :: ⟨128⟩ :: UInt256.ofNat ee.header.timestamp ::
        ⟨8⟩ :: ⟨9566⟩ :: ⟨96⟩ :: ⟨96⟩ :: UInt256.ofNat n :: UInt256.ofNat start :: R)
      (observeInputMem ee.calldata start n) (observeInputAw n) rdata σ k' C' := by
  have hload : memLoad (UInt256.ofNat 64) solcFreePtrMem = UInt256.ofNat 128 :=
    mloadWordValue_of_readWithPadding (by rw [solcFreePtrMem_size]; decide) solcFreePtrMem_read64
  obtain ⟨k1, C1, r1⟩ := uniswapV3Pool_block_9458 (immWords := wordsOf (immStore v)) hov rd
  have haw := observeInputExpansion n hn
  have hfirst : M (M (M (⟨3⟩ : UInt256) (UInt256.ofNat 64) ⟨32⟩)
      (UInt256.ofNat 64) ⟨32⟩) (UInt256.ofNat 128) ⟨32⟩ = ⟨5⟩ := by decide
  simp only [observeInputMem_eq ee start n hn hstart, uniswapV3Pool_block_9458_stack, hload, hfirst] at r1
  change RD (deployedRuntime v) ee g s0 ⟨9538⟩
    (UInt256.div (solcSlotWordAt ⟨0⟩ σ ee) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 184)) ::
      UInt256.ofNat 65535 :: solcSlotWordAt ⟨4⟩ σ ee :: solcSlotWordAt ⟨0⟩ σ ee :: UInt256.ofNat n ::
      UInt256.signextend (UInt256.ofNat 2) (UInt256.div (solcSlotWordAt ⟨0⟩ σ ee)
        (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))) ::
      ⟨128⟩ :: UInt256.ofNat ee.header.timestamp :: ⟨8⟩ :: ⟨9566⟩ :: ⟨96⟩ :: ⟨96⟩ ::
        UInt256.ofNat n :: UInt256.ofNat start :: R)
    (observeInputMem ee.calldata start n) _ rdata σ k1 C1 at r1
  change M (M ⟨5⟩ (UInt256.ofNat 32 + UInt256.ofNat 128)
    (UInt256.mul (UInt256.ofNat 32) (UInt256.ofNat n)))
    (UInt256.ofNat 32 + UInt256.ofNat 128 + UInt256.mul (UInt256.ofNat 32) (UInt256.ofNat n))
    ⟨32⟩ = observeInputAw n at haw
  rw [haw] at r1
  have r2 := uniswapV3Pool_block_9538 (immWords := wordsOf (immStore v))
    (by dsimp only [List.length]; omega)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
  simp only [uniswapV3Pool_block_9538_stack, (observeStorageArgs σ ee).1,
    (observeStorageArgs σ ee).2, ← slot0TickWord σ ee,
    ← slot0FieldShift 23 2 (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 184))
      (UInt256.ofNat 65535) σ ee (by native_decide) (by native_decide)] at r2
  exact ⟨_, _, r2⟩

end Benchmarks.UniswapV3.Pool
