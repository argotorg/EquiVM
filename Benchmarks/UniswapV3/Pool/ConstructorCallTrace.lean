import Benchmarks.UniswapV3.Pool.ConstructorPrefixTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open uniswapV3PoolCreationBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem constructorCallX {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {σ : AccountMap} {aw gasArg : UInt256} {k C : Nat} {rdata : ByteArray}
    (rd : RD (uniswapV3PoolCreationBytecode ++ tail) ee g s0 ⟨89⟩
      [gasArg, UInt256.ofNat ee.source.val, ⟨352⟩, ⟨4⟩, ⟨352⟩, ⟨160⟩,
        ⟨356⟩, ⟨2298697520⟩, UInt256.ofNat ee.source.val, ⟨0⟩]
      (constructorInputMem ee.codeOwner) aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) :
    ∃ (z : Bool) (out : ByteArray) (σ' : AccountMap) (A' : Substate) (k' C' : Nat) (aw' : UInt256),
      callViaEVM evm ee.source 0 constructorParameterCalldata
        (z, {evm with accountMap := σ', substate := A'}, out) false ∧
      RD (uniswapV3PoolCreationBytecode ++ tail) ee g s0 ⟨90⟩
        [if z then ⟨1⟩ else ⟨0⟩, ⟨356⟩, ⟨2298697520⟩, UInt256.ofNat ee.source.val, ⟨0⟩]
        (callOutputMem (constructorInputMem ee.codeOwner) out ⟨352⟩ ⟨160⟩)
        aw' out σ' k' C' ∧ out.size < UInt256.size := by
  have hd : decode (uniswapV3PoolCreationBytecode ++ tail) ⟨89⟩ = some (.STATICCALL, none) :=
    decode_append_left_of_decode _ _ _ _ _ (by native_decide) (by native_decide) (by decide)
  obtain ⟨z, out, σ', A', k', C', hc, rn, hb⟩ := RD.staticcallSource rd hd
    (by change 5 ≤ 1024; decide) hs.accounts.symm hs.world hs.env
  refine ⟨z, out, σ', A', k', C', _, ?_, rn, hb⟩
  have ha : AccountAddress.ofUInt256 (UInt256.ofNat ee.source.val) = ee.source :=
    accountAddress_of_word_val_tail _
  change callViaEVM evm (AccountAddress.ofUInt256 (UInt256.ofNat ee.source.val)) 0
    ((constructorInputMem ee.codeOwner).readWithPadding 352 4) _ false at hc
  simpa only [ha, constructorInputMem_calldata] using hc

theorem constructorCallFailedX {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {σ : AccountMap} {aw : UInt256} {k C : Nat} {mem out : ByteArray}
    (rd : RD (uniswapV3PoolCreationBytecode ++ tail) ee g s0 ⟨90⟩
      [⟨0⟩, ⟨356⟩, ⟨2298697520⟩, UInt256.ofNat ee.source.val, ⟨0⟩]
      mem aw out σ k C) : RDrev (uniswapV3PoolCreationBytecode ++ tail) g s0 := by
  have rb := uniswapV3PoolCreation_block_90_fallthrough (by change 7 ≤ 1024; decide)
    (by decide) rd
  exact uniswapV3PoolCreation_block_98 (by change 8 ≤ 1024; decide) rb

theorem constructorCallSuccessX {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {σ : AccountMap} {aw : UInt256} {k C : Nat} {mem out : ByteArray}
    (rd : RD (uniswapV3PoolCreationBytecode ++ tail) ee g s0 ⟨90⟩
      [⟨1⟩, ⟨356⟩, ⟨2298697520⟩, UInt256.ofNat ee.source.val, ⟨0⟩]
      mem aw out σ k C) :
    ∃ k' C', RD (uniswapV3PoolCreationBytecode ++ tail) ee g s0 ⟨107⟩
      [⟨0⟩, ⟨356⟩, ⟨2298697520⟩, UInt256.ofNat ee.source.val, ⟨0⟩]
      mem aw out σ k' C' := by
  have rn := uniswapV3PoolCreation_block_90_taken (by change 7 ≤ 1024; decide)
    (by decide) (by native_decide) rd
  exact ⟨_, _, rn⟩

theorem constructorShortDataX {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {σ : AccountMap} {aw : UInt256} {k C : Nat} {mem out : ByteArray}
    (rd : RD (uniswapV3PoolCreationBytecode ++ tail) ee g s0 ⟨107⟩
      [⟨0⟩, ⟨356⟩, ⟨2298697520⟩, UInt256.ofNat ee.source.val, ⟨0⟩]
      mem aw out σ k C) (hshort : out.size < 160) :
    RDrev (uniswapV3PoolCreationBytecode ++ tail) g s0 := by
  have hl : UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 160) = ⟨1⟩ := by
    apply ult_one
    rw [ulit_toNat' out.size (by change out.size < 2 ^ 256; omega)]
    exact hshort
  have rb := uniswapV3PoolCreation_block_107_fallthrough (by decide) (by rw [hl]; decide) rd
  exact uniswapV3PoolCreation_block_126 (by change 5 ≤ 1024; decide) rb

theorem constructorBeforeFieldsX {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {σ : AccountMap} {aw : UInt256} {k C : Nat} {out : ByteArray}
    (rd : RD (uniswapV3PoolCreationBytecode ++ tail) ee g s0 ⟨107⟩
      [⟨0⟩, ⟨356⟩, ⟨2298697520⟩, UInt256.ofNat ee.source.val, ⟨0⟩]
      (callOutputMem (constructorInputMem ee.codeOwner) out ⟨352⟩ ⟨160⟩) aw out σ k C)
    (hlen : 160 ≤ out.size) (hb : out.size < UInt256.size) :
    ∃ k' C' aw', RD (uniswapV3PoolCreationBytecode ++ tail) ee g s0 ⟨130⟩
      [UInt256.ofNat out.size, ⟨352⟩, ⟨0⟩] (constructorOutputMem ee.codeOwner out)
      aw' out σ k' C' := by
  have hl : UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 160) = ⟨0⟩ := by
    apply ult_zero
    rw [ulit_toNat' out.size hb]
    exact hlen
  rw [constructorCallOutput_eq _ _ hlen hb] at rd
  have rn := uniswapV3PoolCreation_block_107_taken (by decide) (by rw [hl]; decide)
    (by native_decide) rd
  simp only [uniswapV3PoolCreation_block_107_taken_stack] at rn
  have hm : memLoad (UInt256.ofNat 64) (constructorOutputMem ee.codeOwner out) = ⟨352⟩ :=
    constructorOutputMem_load64 _ _ hlen
  rw [hm] at rn
  exact ⟨_, _, _, rn⟩

end Benchmarks.UniswapV3.Pool
