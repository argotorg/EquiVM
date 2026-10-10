import Benchmarks.UniswapV3.Pool.Common
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_005
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_007

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks

namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: Reasoning.Dispatch, eliminate all other selector arms from one match.
theorem selectorMismatch_of_match {I : ExecutionEnv} {s t : ByteArray}
    (hmatch : (t == I.calldata.extract 0 4) = true) (hne : s ≠ t) :
    ¬ (s == I.calldata.extract 0 4) = true := by
  intro hs
  exact hne ((byteArray_eq_of_beq hs).trans (byteArray_eq_of_beq hmatch).symm)

-- LIBRARY CANDIDATE: Reasoning.Solc, scalar return after writes to the hashing scratch space.
theorem solcScratchScalarReturnBytes (w : UInt256) (scratch : ByteArray)
    (hscratch : scratch.size = 96)
    (hread64 : scratch.readWithPadding 64 32 = (⟨128⟩ : UInt256).toByteArray) :
    (w.toByteArray.write 0 scratch
      (memLoad (UInt256.ofNat 64) scratch).toNat 32).readWithPadding
        (memLoad (UInt256.ofNat 64) (w.toByteArray.write 0 scratch
          (memLoad (UInt256.ofNat 64) scratch).toNat 32)).toNat
        ((UInt256.ofNat 32) + UInt256.sub (memLoad (UInt256.ofNat 64) scratch)
          (memLoad (UInt256.ofNat 64) (w.toByteArray.write 0 scratch
            (memLoad (UInt256.ofNat 64) scratch).toNat 32))).toNat = w.toByteArray := by
  have hload : memLoad (UInt256.ofNat 64) scratch = ⟨128⟩ := mloadFreePtrValue (by rw [hscratch]; decide) hread64
  rw [hload]
  change (solcScratchReturnMem scratch w).readWithPadding
    (memLoad (UInt256.ofNat 64) (solcScratchReturnMem scratch w)).toNat
    ((UInt256.ofNat 32) + UInt256.sub ⟨128⟩ (memLoad (UInt256.ofNat 64) (solcScratchReturnMem scratch w))).toNat = _
  have hretload : memLoad (UInt256.ofNat 64) (solcScratchReturnMem scratch w) = ⟨128⟩ := solcScratchReturnMem_mload64 w hscratch hread64
  rw [hretload]
  exact solcScratchReturnMem_read128 w hscratch

-- LIBRARY CANDIDATE: Reasoning.Solc, normalize the scalar encoder's returned memory slice.
theorem solcScalarReturnBytes (w : UInt256) :
    (w.toByteArray.write 0 solcFreePtrMem
      (memLoad (UInt256.ofNat 64) solcFreePtrMem).toNat 32).readWithPadding
        (memLoad (UInt256.ofNat 64) (w.toByteArray.write 0 solcFreePtrMem
          (memLoad (UInt256.ofNat 64) solcFreePtrMem).toNat 32)).toNat
        ((UInt256.ofNat 32) + UInt256.sub (memLoad (UInt256.ofNat 64) solcFreePtrMem)
          (memLoad (UInt256.ofNat 64) (w.toByteArray.write 0 solcFreePtrMem
            (memLoad (UInt256.ofNat 64) solcFreePtrMem).toNat 32))).toNat = w.toByteArray := by
  exact solcScratchScalarReturnBytes w solcFreePtrMem solcFreePtrMem_size solcFreePtrMem_read64

set_option maxRecDepth 10000 in
theorem RD.poolReturnAddress {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {v : UniswapV3PoolImmutables} {val aw : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : AccountMap}
    (h : RD (deployedRuntime v) ee g s0 ⟨443⟩ (val :: R)
      solcFreePtrMem aw rdata acc k C)
    (hov : R.length + 6 ≤ 1024) :
    RDret (deployedRuntime v) g s0 acc
      (UInt256.toByteArray (UInt256.land val solcAddrMask)) := by
  have hret := uniswapV3Pool_block_443 (immWords := wordsOf (immStore v)) hov h
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1) = solcAddrMask := by native_decide
  simpa only [solcScalarReturnBytes, hmask] using hret

-- LIBRARY CANDIDATE: Reasoning.ABI, specialize the masked-address encoding to an address.
theorem addressReturnEncoding (a : AccountAddress) :
    encodeReturnValue? (.elem .address) (.address a) =
      some (UInt256.toByteArray (EVM.word a.val)) := by
  simpa only [addressWord_val_clean, accountAddress_of_word_val] using
    solcAddressReturnEncoding rfl (EVM.word a.val)

-- LIBRARY CANDIDATE: Reasoning.WordArithmetic, relate unsigned casts to EVM masking.
theorem normalizeUIntWord_mask (width : ABI.BitWidth) (w mask : UInt256)
    (hmask : mask.toNat = 2 ^ width.val - 1) :
    normalizeInt (.uint width) (Int.ofNat w.toNat) =
      Int.ofNat (UInt256.land w mask).toNat := by
  rw [normalizeInt, uland_toNat, hmask]
  change (Int.ofNat w.toNat) % (Int.ofNat (2 ^ width.val)) =
    Int.ofNat (Nat.land w.toNat (2 ^ width.val - 1))
  rw [nat_land_mask_eq_mod]
  rfl

-- LIBRARY CANDIDATE: Reasoning.ABI, encode the result of an unsigned narrowing cast.
theorem uintCastReturnEncoding (width : ABI.BitWidth) (w mask : UInt256)
    (hmask : mask.toNat = 2 ^ width.val - 1) :
    encodeReturnValue? (.elem (.int (.uint width)))
      (.int (normalizeInt (.uint width) (Int.ofNat w.toNat))) =
        some (UInt256.toByteArray (UInt256.land w mask)) := by
  rw [normalizeUIntWord_mask width w mask hmask]
  exact uintReturnEncoding width _ (u256LandMaskToNatLtOfToNat w mask hmask)

-- LIBRARY CANDIDATE: Reasoning.SolmBody, evaluate an explicit integer cast.
theorem evalExpr_intCast {cfg : Config} {frame : Frame} {evm : EVM.State}
    {expr : Expr} {i : Int} (ty : ABI.IntType)
    (h : evalExpr? cfg frame evm expr = .ok (.int i)) :
    evalExpr? cfg frame evm (.cast expr (.elem (.int ty))) =
      .ok (.int (normalizeInt ty i)) := by
  simp only [evalExpr?, h, bind, EvalResult.bind, castValue_int, EvalResult.ofOption]

-- LIBRARY CANDIDATE: Reasoning.WordArithmetic, the solc uint128 cleanup mask.
theorem solcMask128 : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
    (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 128 - 1) := by native_decide

theorem RD.poolReturnUint128 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {v : UniswapV3PoolImmutables} {val aw : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : AccountMap}
    (h : RD (deployedRuntime v) ee g s0 ⟨654⟩ (val :: R)
      solcFreePtrMem aw rdata acc k C)
    (hov : R.length + 6 ≤ 1024) :
    RDret (deployedRuntime v) g s0 acc
      (UInt256.toByteArray (UInt256.land val (UInt256.ofNat (2 ^ 128 - 1)))) := by
  have hret := uniswapV3PoolBlocks.uniswapV3Pool_block_654
    (immWords := wordsOf (immStore v)) hov h
  simpa only [solcScalarReturnBytes, solcMask128] using hret

theorem RD.poolReturnWordFromScratch {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {v : UniswapV3PoolImmutables} {val aw : UInt256} {R : List UInt256}
    {rdata scratch : ByteArray} {acc : AccountMap}
    (h : RD (deployedRuntime v) ee g s0 ⟨1118⟩ (val :: R)
      scratch aw rdata acc k C)
    (hscratch : scratch.size = 96)
    (hread64 : scratch.readWithPadding 64 32 = (⟨128⟩ : UInt256).toByteArray)
    (hov : R.length + 4 ≤ 1024) :
    RDret (deployedRuntime v) g s0 acc (UInt256.toByteArray val) := by
  have hret := uniswapV3PoolBlocks.uniswapV3Pool_block_1118
    (immWords := wordsOf (immStore v)) hov h
  simpa only [solcScratchScalarReturnBytes val scratch hscratch hread64] using hret

theorem RD.poolReturnWord {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {v : UniswapV3PoolImmutables} {val aw : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : AccountMap}
    (h : RD (deployedRuntime v) ee g s0 ⟨1118⟩ (val :: R)
      solcFreePtrMem aw rdata acc k C)
    (hov : R.length + 4 ≤ 1024) :
    RDret (deployedRuntime v) g s0 acc (UInt256.toByteArray val) := by
  exact RD.poolReturnWordFromScratch (v := v) h solcFreePtrMem_size solcFreePtrMem_read64 hov

end Benchmarks.UniswapV3.Pool
