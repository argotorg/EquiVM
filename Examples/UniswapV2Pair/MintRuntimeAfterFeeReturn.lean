import Examples.UniswapV2Pair.MintRuntimeAfterFeeUpdate

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

theorem uniswapMintLogMem_size
    (amount0 amount1 : UInt256) {mem : ByteArray} (hmem : mem.size = 192) :
    (uniswapMintLogMem amount0 amount1 mem).size = 192 := by
  unfold uniswapMintLogMem
  have hamount0 :
      ((UInt256.toByteArray amount0).write 0 mem 128 32).size = 192 := by
    exact toByteArray_write32_size_of_le mem amount0 128 192 192 hmem
      (by rw [hmem]; omega) (by omega)
  exact toByteArray_write32_size_of_le
    ((UInt256.toByteArray amount0).write 0 mem 128 32) amount1 160 192 192 hamount0
    (by rw [hamount0]; omega) (by omega)

theorem uniswapMintLogMem_read64
    (amount0 amount1 : UInt256) {mem : ByteArray}
    (hmem : mem.size = 192)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (uniswapMintLogMem amount0 amount1 mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold uniswapMintLogMem
  have hamount0 :
      ((UInt256.toByteArray amount0).write 0 mem 128 32).size = 192 := by
    exact toByteArray_write32_size_of_le mem amount0 128 192 192 hmem
      (by rw [hmem]; omega) (by omega)
  rw [write32_read_below _ _ 160 64 (by rw [toByteArray_size])
      (by rw [hamount0]; omega) (by omega)]
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
      (by rw [hmem]; omega) (by omega)]
  exact hmem64

theorem uniswapMintLogMem_mload64
    (amount0 amount1 : UInt256) {mem : ByteArray}
    (hmem : mem.size = 192)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (uniswapMintLogMem amount0 amount1 mem).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((uniswapMintLogMem amount0 amount1 mem).readWithPadding (⟨64⟩ : UInt256).toNat
          32))) =
      ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [uniswapMintLogMem_size amount0 amount1 hmem]; decide)
    (uniswapMintLogMem_read64 amount0 amount1 hmem hmem64)

theorem uniswapMintReturnMem_size
    (liquidity amount0 amount1 : UInt256) {mem : ByteArray} (hmem : mem.size = 192) :
    (uniswapMintReturnMem liquidity amount0 amount1 mem).size = 192 := by
  unfold uniswapMintReturnMem
  exact toByteArray_write32_size_of_le
    (uniswapMintLogMem amount0 amount1 mem) liquidity 128 192 192
    (uniswapMintLogMem_size amount0 amount1 hmem)
    (by rw [uniswapMintLogMem_size amount0 amount1 hmem]; omega) (by omega)

theorem uniswapMintReturnMem_read64
    (liquidity amount0 amount1 : UInt256) {mem : ByteArray}
    (hmem : mem.size = 192)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (uniswapMintReturnMem liquidity amount0 amount1 mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold uniswapMintReturnMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
      (by rw [uniswapMintLogMem_size amount0 amount1 hmem]; omega) (by omega),
    uniswapMintLogMem_read64 amount0 amount1 hmem hmem64]

theorem uniswapMintReturnMem_mload64
    (liquidity amount0 amount1 : UInt256) {mem : ByteArray}
    (hmem : mem.size = 192)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (uniswapMintReturnMem liquidity amount0 amount1 mem).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((uniswapMintReturnMem liquidity amount0 amount1 mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [uniswapMintReturnMem_size liquidity amount0 amount1 hmem]; decide)
    (uniswapMintReturnMem_read64 liquidity amount0 amount1 hmem hmem64)

theorem uniswapMintReturnMem_read128
    (liquidity amount0 amount1 : UInt256) {mem : ByteArray} (hmem : mem.size = 192) :
    (uniswapMintReturnMem liquidity amount0 amount1 mem).readWithPadding 128 32 =
      UInt256.toByteArray liquidity := by
  unfold uniswapMintReturnMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [uniswapMintLogMem_size amount0 amount1 hmem]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray liquidity).size ≤ 32
    rw [toByteArray_size])

set_option maxHeartbeats 1000000 in
/- Runtime-only Mint suffix from the post-`_update` rejoin: emit `Mint`, unlock the pair, clean
the stack, and jump to the shared uint256 return wrapper at pc 861. -/
theorem uniswapMintRuntimeFinalizeToReturnWrapper
    {s0 : State} {I : ExecutionEnv} {g : UInt256}
    {σPost : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {totalSupply feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd3974 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨3974⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata σPost k C)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hlogMload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (uniswapMintLogMem amount0 amount1 mem).size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          ((uniswapMintLogMem amount0 amount1 mem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hperm : I.perm = true) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨861⟩
      [liquidity, sel]
      (uniswapMintLogMem amount0 amount1 mem) feeToStaticcallActiveWords rdata
      (sstoreAccountMap I.codeOwner σPost ⟨12⟩ (⟨1⟩ : UInt256)) k' C' := by
  let memAmount0 := (UInt256.toByteArray amount0).write 0 mem 128 32
  have rd3978 := evm_run rd3974 with [jumpdest, push1 ⟨64⟩, dup1]
  have rd3979 := rd3978.mload 0 ⟨128⟩ feeToStaticcallActiveWords
    (by native_decide) mem_cost hmload64 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3981 := evm_run rd3979 with [dup6, dup2]
  have rd3982 := rd3981.mstore 0 memAmount0 feeToStaticcallActiveWords
    (by native_decide) mem_cost (by unfold memAmount0; rfl) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3988pre := evm_run rd3982 with [push1 ⟨32⟩, dup2, add, dup6, swap1]
  have rd3989 := rd3988pre.mstore 0 (uniswapMintLogMem amount0 amount1 mem)
    feeToStaticcallActiveWords (by native_decide) mem_cost
    (by unfold uniswapMintLogMem memAmount0; rfl) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3992 := evm_run rd3989 with [
    dup2,
    raw mload 0 ⟨128⟩ feeToStaticcallActiveWords (by native_decide)
      mem_cost hlogMload64 (by native_decide) (by evm_ov),
    caller, swap3]
  have rd4026 := rd3992.pushConst uniswapMintTopic (width := 32) (op := .PUSH32)
    (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd4032 := evm_run rd4026 with [swap3, dup3, swap1, sub, add, swap1]
  have rd4033 := RD.uniswapLog2 0 feeToStaticcallActiveWords rd4032
    (by native_decide) hperm mem_cost (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd4039pre := evm_run rd4033 with [pop, pop, push1 ⟨1⟩, push1 ⟨12⟩]
  obtain ⟨_, _, rd4040⟩ := rd4039pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd4050 := evm_run rd4040 with [
    pop, swap5, swap7, swap6, pop, pop, pop, pop, pop, pop]
  exact ⟨_, _, rd4050.jump (by native_decide) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)⟩

theorem RD.uniswapReturnWord861FromFeeMem {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {val ret : UInt256} {R : List UInt256} {mem memout rdata : ByteArray}
    {acc : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨861⟩ (val :: ret :: R)
      mem feeToStaticcallActiveWords rdata acc k C)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hmemout : (UInt256.toByteArray val).write 0 mem 128 32 = memout)
    (hmemoutLoad64 :
      (if (⟨64⟩ : UInt256).toNat ≥ memout.size then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memout.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hread128 : memout.readWithPadding 128 32 = UInt256.toByteArray val)
    (hov : R.length + 5 ≤ 1024) :
    RDret UniswapV2Pair.uniswapV2PairBytecode g s0 acc (UInt256.toByteArray val) := by
  exact evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ feeToStaticcallActiveWords (by native_decide)
      mem_cost hmload64 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw mstore 0 memout feeToStaticcallActiveWords (by native_decide)
      mem_cost hmemout (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ feeToStaticcallActiveWords (by native_decide)
      mem_cost hmemoutLoad64 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw ret 0 (UInt256.toByteArray val) (by native_decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨32⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat =
            32 from by decide]
        exact hread128)
      (by evm_ov)]

set_option maxHeartbeats 1000000 in
/- Runtime-only Mint suffix from the post-`_update` rejoin through the final ABI `uint256`
return. -/
theorem uniswapMintRuntimeFinalizeReturns
    {s0 : State} {I : ExecutionEnv} {g : UInt256}
    {σPost : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {totalSupply feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd3974 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨3974⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata σPost k C)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hlogMload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (uniswapMintLogMem amount0 amount1 mem).size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          ((uniswapMintLogMem amount0 amount1 mem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hretMload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (uniswapMintReturnMem liquidity amount0 amount1 mem).size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          ((uniswapMintReturnMem liquidity amount0 amount1 mem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hretRead128 :
      (uniswapMintReturnMem liquidity amount0 amount1 mem).readWithPadding 128 32 =
        UInt256.toByteArray liquidity)
    (hperm : I.perm = true) :
    RDret uniswapV2PairBytecode (Sat256.ofUInt256 g)
      s0
      (sstoreAccountMap I.codeOwner σPost ⟨12⟩ (⟨1⟩ : UInt256))
      (UInt256.toByteArray liquidity) := by
  obtain ⟨_, _, rd861⟩ :=
    uniswapMintRuntimeFinalizeToReturnWrapper rd3974 hmload64 hlogMload64 hperm
  exact RD.uniswapReturnWord861FromFeeMem
    (val := liquidity) (ret := sel) (R := []) rd861 hlogMload64
    (by unfold uniswapMintReturnMem; rfl)
    hretMload64 hretRead128
    (by simp only [List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only Mint suffix after `_update` through the final ABI return, fee-off branch. -/
theorem uniswapMintRuntimeAfterUpdateFeeOffReturns
    {s0 : State} {I : ExecutionEnv} {g : UInt256}
    {σUpd : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {totalSupply feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd3926 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨3926⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata σUpd k C)
    (hfeeOff : feeOn = ⟨0⟩)
    (hmem : mem.size = 192)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hperm : I.perm = true) :
    RDret uniswapV2PairBytecode (Sat256.ofUInt256 g)
      s0
      (sstoreAccountMap I.codeOwner σUpd ⟨12⟩ (⟨1⟩ : UInt256))
      (UInt256.toByteArray liquidity) := by
  obtain ⟨_, _, rd3974⟩ := uniswapMintRuntimeAfterUpdateFeeOff rd3926 hfeeOff
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) hmem64
  exact uniswapMintRuntimeFinalizeReturns rd3974 hmload64
    (uniswapMintLogMem_mload64 amount0 amount1 hmem hmem64)
    (uniswapMintReturnMem_mload64 liquidity amount0 amount1 hmem hmem64)
    (uniswapMintReturnMem_read128 liquidity amount0 amount1 hmem) hperm

set_option maxHeartbeats 1000000 in
/- Runtime-only Mint suffix after `_update` through the final ABI return, fee-on branch. -/
theorem uniswapMintRuntimeAfterUpdateFeeOnReturns
    {s0 : State} {I : ExecutionEnv} {g : UInt256}
    {σUpd : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {totalSupply feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd3926 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨3926⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata σUpd k C)
    (hfeeOn : feeOn ≠ ⟨0⟩)
    (hfit :
      (UInt256.land (uniswapSlotWord ⟨8⟩ σUpd I) reserve112Mask).toNat *
          (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σUpd I) reserve112Shift)
            reserve112Mask).toNat < UInt256.size)
    (hmem : mem.size = 192)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hperm : I.perm = true) :
    RDret uniswapV2PairBytecode (Sat256.ofUInt256 g)
      s0
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σUpd ⟨11⟩
          (UInt256.mul (UInt256.land (uniswapSlotWord ⟨8⟩ σUpd I) reserve112Mask)
            (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σUpd I) reserve112Shift)
              reserve112Mask))) ⟨12⟩ (⟨1⟩ : UInt256))
      (UInt256.toByteArray liquidity) := by
  obtain ⟨_, _, rd3974⟩ := uniswapMintRuntimeAfterUpdateFeeOn rd3926 hfeeOn hfit hperm
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) hmem64
  exact uniswapMintRuntimeFinalizeReturns rd3974 hmload64
    (uniswapMintLogMem_mload64 amount0 amount1 hmem hmem64)
    (uniswapMintReturnMem_mload64 liquidity amount0 amount1 hmem hmem64)
    (uniswapMintReturnMem_read128 liquidity amount0 amount1 hmem) hperm



end UniswapV2Pair
