import Examples.UniswapV2Pair.MintFeeFactoryCallRuntime
import Examples.UniswapV2Pair.MintFeeBranchRuntime
import Examples.UniswapV2Pair.MintRuntimeBalance

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` slice from routine entry to the factory `feeTo()` code-existence
guard. -/
theorem uniswapMintFeeRuntimeFactoryExtcodesize
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA'' : Batteries.RBSet AccountAddress compare} {σ'' : AccountMap}
    {o o1 : ByteArray} {k C : ℕ} {amount0 amount1 balance0 balance1 toWord sel : UInt256}
    (rd7696 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7696⟩
      [reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
      balanceOfThisStaticcallActiveWords o1 (cA'', σ'') k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7765⟩
      [mintFeeFactoryWord σ'' I, mintFeeFactoryWord σ'' I,
        ⟨128⟩, ⟨4⟩, ⟨128⟩, ⟨32⟩, ⟨132⟩, feeToSelectorWord,
        mintFeeFactoryWord σ'' I, ⟨0⟩, ⟨0⟩,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (feeToSelectorMem (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1))
      feeToStaticcallActiveWords o1 (cA'', σ'') k' C' := by
  exact uniswapMintFeeRuntimeFactoryExtcodesizeOfTail rd7696
    (by rw [balanceOfThisRebuiltStaticcallMem_size_of_size_ge
      (UInt256.ofNat I.codeOwner.val) o o1 ho32 hoSize ho132 ho1Size]; omega)
    (balanceOfThisRebuiltStaticcallMem_read64_of_size_ge
      (UInt256.ofNat I.codeOwner.val) o o1 ho32 hoSize ho132 ho1Size)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` reverts when the factory account has no deployed code. -/
theorem uniswapMintFeeRuntimeFactoryMissingCodeReverts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA'' : Batteries.RBSet AccountAddress compare} {σ'' : AccountMap}
    {o o1 : ByteArray} {k C : ℕ} {amount0 amount1 balance0 balance1 toWord sel : UInt256}
    (rd7765 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7765⟩
      [mintFeeFactoryWord σ'' I, mintFeeFactoryWord σ'' I,
        ⟨128⟩, ⟨4⟩, ⟨128⟩, ⟨32⟩, ⟨132⟩, feeToSelectorWord,
        mintFeeFactoryWord σ'' I, ⟨0⟩, ⟨0⟩,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (feeToSelectorMem (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1))
      feeToStaticcallActiveWords o1 (cA'', σ'') k C)
    (hfactoryNoCode : extCodeSizeWord σ'' (mintFeeFactoryWord σ'' I) = ⟨0⟩) :
    RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact uniswapMintFeeRuntimeFactoryMissingCodeRevertsOfTail rd7765 hfactoryNoCode
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` slice through the factory `feeTo()` `STATICCALL`, exposing the
shared `Θ` result. -/
theorem uniswapMintFeeRuntimeFactoryStaticcallMade
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA'' : Batteries.RBSet AccountAddress compare} {σ'' : AccountMap}
    {o o1 : ByteArray} {k C : ℕ} {amount0 amount1 balance0 balance1 toWord sel : UInt256}
    (rd7765 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7765⟩
      [mintFeeFactoryWord σ'' I, mintFeeFactoryWord σ'' I,
        ⟨128⟩, ⟨4⟩, ⟨128⟩, ⟨32⟩, ⟨132⟩, feeToSelectorWord,
        mintFeeFactoryWord σ'' I, ⟨0⟩, ⟨0⟩,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (feeToSelectorMem (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1))
      feeToStaticcallActiveWords o1 (cA'', σ'') k C)
    (hdepth : I.depth.val < 1024)
    (hfactoryCode : extCodeSizeWord σ'' (mintFeeFactoryWord σ'' I) ≠ ⟨0⟩) :
    ∃ (cAFee : Batteries.RBSet AccountAddress compare) (σFee : AccountMap)
      (zFee : Bool) (outFee : ByteArray) (A_inFee : Substate) (callGasFee : UInt256)
      (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cAFee, σFee, g'', A', zFee, outFee) = Ethereum.EVM.Θ I.blobVersionedHashes
          cA'' gh bl σ'' σ₀ A_inFee
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
          (AccountAddress.ofUInt256 (mintFeeFactoryWord σ'' I))
          (toExecute σ'' (AccountAddress.ofUInt256 (mintFeeFactoryWord σ'' I)))
          callGasFee (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((feeToSelectorMem
            (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)).readWithPadding
              128 4)
          (I.depth + 1) I.header false)
      ∧ RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7781⟩
          [(if zFee then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨132⟩,
            feeToSelectorWord, mintFeeFactoryWord σ'' I, ⟨0⟩, ⟨0⟩,
            reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
            reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
            ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
            reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
            reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
            ⟨0⟩, toWord, ⟨861⟩, sel]
          (feeToStaticcallMem
            (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
            outFee)
          feeToStaticcallActiveWords outFee (cAFee, σFee) k' C'
      ∧ outFee.size < UInt256.size := by
  exact uniswapMintFeeRuntimeFactoryStaticcallMadeOfTail rd7765 hdepth hfactoryCode
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1500000 in
/- Runtime-only `_mintFee` branches after the factory `feeTo()` call. -/
theorem uniswapMintFeeRuntimeFactoryResultBranchesFromCall
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {σ'' : AccountMap} {o o1 outFee : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 toWord sel : UInt256} {zFee : Bool}
    (rd7781 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7781⟩
      [(if zFee then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨132⟩,
        feeToSelectorWord, mintFeeFactoryWord σ'' I, ⟨0⟩, ⟨0⟩,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee)
      feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size)
    (houtFeeSize : outFee.size < UInt256.size) :
    (zFee = false →
      RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))
    ∧ (zFee = true → outFee.size < 32 →
      RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))
    ∧ (zFee = true → 32 ≤ outFee.size →
      ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7825⟩
        [mintFeeKLastSlotWord σFee I,
          UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)),
          ⟨0⟩, ⟨0⟩,
          reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
          reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
          ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
          reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
          reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
          ⟨0⟩, toWord, ⟨861⟩, sel]
        (feeToStaticcallMem
          (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
          outFee)
        feeToStaticcallActiveWords outFee (cAFee, σFee) k' C') := by
  exact uniswapMintFeeRuntimeFactoryResultBranchesFromCallOfTail rd7781
    (by rw [balanceOfThisRebuiltStaticcallMem_size_of_size_ge
      (UInt256.ofNat I.codeOwner.val) o o1 ho32 hoSize ho132 ho1Size]; omega)
    (balanceOfThisRebuiltStaticcallMem_read64_of_size_ge
      (UInt256.ofNat I.codeOwner.val) o o1 ho32 hoSize ho132 ho1Size) houtFeeSize
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` fee-off slice from the decoded `feeTo`/loaded `kLast` state to the
fee-off branch entry. -/
theorem uniswapMintFeeRuntimeFeeOffEntry
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd7825 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7825⟩
      [kLast, feeTo, ⟨0⟩, ⟨0⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hfeeToZero : UInt256.land feeTo solcAddrMask = ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8026⟩
      [kLast, feeTo, ⟨0⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  exact uniswapMintFeeRuntimeFeeOffEntryOfTail
    rd7825 hfeeToZero
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` fee-off return when `kLast` is already zero. -/
theorem uniswapMintFeeRuntimeFeeOffKLastZeroReturn
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd8026 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8026⟩
      [kLast, feeTo, ⟨0⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hkLastZero : kLast = ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨0⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord,
        ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  exact uniswapMintFeeRuntimeFeeOffKLastZeroReturnOfTail
    rd8026 hkLastZero (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` fee-off return when `kLast` is nonzero, clearing slot 11 first. -/
theorem uniswapMintFeeRuntimeFeeOffKLastNonzeroReturn
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd8026 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8026⟩
      [kLast, feeTo, ⟨0⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hperm : I.perm = true) (hkLastNonzero : kLast ≠ ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨0⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord,
        ⟨861⟩, sel]
      mem aw rdata (cAFee, sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩) k' C' := by
  exact uniswapMintFeeRuntimeFeeOffKLastNonzeroReturnOfTail
    rd8026 hperm hkLastNonzero (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` fee-on slice from the decoded `feeTo`/loaded `kLast` state to the
fee-on branch entry. -/
theorem uniswapMintFeeRuntimeFeeOnEntry
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd7825 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7825⟩
      [kLast, feeTo, ⟨0⟩, ⟨0⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hfeeToNonzero : UInt256.land feeTo solcAddrMask ≠ ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7848⟩
      [kLast, feeTo, ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  exact uniswapMintFeeRuntimeFeeOnEntryOfTail
    rd7825 hfeeToNonzero
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` fee-on return when `kLast` is zero. -/
theorem uniswapMintFeeRuntimeFeeOnKLastZeroReturn
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd7848 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7848⟩
      [kLast, feeTo, ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hkLastZero : kLast = ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord,
        ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  exact uniswapMintFeeRuntimeFeeOnKLastZeroReturnOfTail
    rd7848 hkLastZero (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` fee-off decoded branch returning with zero `kLast`. -/
theorem uniswapMintFeeRuntimeFeeOffKLastZeroFromDecodeReturn
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd7825 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7825⟩
      [kLast, feeTo, ⟨0⟩, ⟨0⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hfeeToZero : UInt256.land feeTo solcAddrMask = ⟨0⟩)
    (hkLastZero : kLast = ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨0⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord,
        ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  obtain ⟨_, _, rd8026⟩ := uniswapMintFeeRuntimeFeeOffEntry rd7825 hfeeToZero
  exact uniswapMintFeeRuntimeFeeOffKLastZeroReturn rd8026 hkLastZero

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` fee-off decoded branch returning after clearing nonzero `kLast`. -/
theorem uniswapMintFeeRuntimeFeeOffKLastNonzeroFromDecodeReturn
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd7825 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7825⟩
      [kLast, feeTo, ⟨0⟩, ⟨0⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hfeeToZero : UInt256.land feeTo solcAddrMask = ⟨0⟩)
    (hperm : I.perm = true)
    (hkLastNonzero : kLast ≠ ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨0⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord,
        ⟨861⟩, sel]
      mem aw rdata (cAFee, sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩) k' C' := by
  obtain ⟨_, _, rd8026⟩ := uniswapMintFeeRuntimeFeeOffEntry rd7825 hfeeToZero
  exact uniswapMintFeeRuntimeFeeOffKLastNonzeroReturn rd8026 hperm hkLastNonzero

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` fee-on decoded branch returning when `kLast` is zero. -/
theorem uniswapMintFeeRuntimeFeeOnKLastZeroFromDecodeReturn
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd7825 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7825⟩
      [kLast, feeTo, ⟨0⟩, ⟨0⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hfeeToNonzero : UInt256.land feeTo solcAddrMask ≠ ⟨0⟩)
    (hkLastZero : kLast = ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord,
        ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  obtain ⟨_, _, rd7848⟩ := uniswapMintFeeRuntimeFeeOnEntry rd7825 hfeeToNonzero
  exact uniswapMintFeeRuntimeFeeOnKLastZeroReturn rd7848 hkLastZero

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` factory-call success path returning fee-off with zero `kLast`. -/
theorem uniswapMintFeeRuntimeFactoryResultFeeOffKLastZeroReturn
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σ'' : AccountMap}
    {o o1 outFee : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 toWord sel : UInt256} {zFee : Bool}
    (rd7781 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7781⟩
      [(if zFee then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨132⟩,
        feeToSelectorWord, mintFeeFactoryWord σ'' I, ⟨0⟩, ⟨0⟩,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee)
      feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size)
    (houtFeeSize : outFee.size < UInt256.size)
    (hzFee : zFee = true)
    (hout32 : 32 ≤ outFee.size)
    (hfeeToZero :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
          solcAddrMask =
        ⟨0⟩)
    (hkLastZero : mintFeeKLastSlotWord σFee I = ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨0⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee)
      feeToStaticcallActiveWords outFee (cAFee, σFee) k' C' := by
  obtain ⟨_, _, hdecoded⟩ :=
    uniswapMintFeeRuntimeFactoryResultBranchesFromCall rd7781 ho32 hoSize ho132 ho1Size
      houtFeeSize
  obtain ⟨_, _, rd7825⟩ := hdecoded hzFee hout32
  exact uniswapMintFeeRuntimeFeeOffKLastZeroFromDecodeReturn rd7825 hfeeToZero hkLastZero

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` factory-call success path returning fee-off after clearing nonzero
`kLast`. -/
theorem uniswapMintFeeRuntimeFactoryResultFeeOffKLastNonzeroReturn
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σ'' : AccountMap}
    {o o1 outFee : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 toWord sel : UInt256} {zFee : Bool}
    (rd7781 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7781⟩
      [(if zFee then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨132⟩,
        feeToSelectorWord, mintFeeFactoryWord σ'' I, ⟨0⟩, ⟨0⟩,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee)
      feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size)
    (houtFeeSize : outFee.size < UInt256.size)
    (hzFee : zFee = true)
    (hout32 : 32 ≤ outFee.size)
    (hfeeToZero :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
          solcAddrMask =
        ⟨0⟩)
    (hperm : I.perm = true)
    (hkLastNonzero : mintFeeKLastSlotWord σFee I ≠ ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨0⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee)
      feeToStaticcallActiveWords outFee
      (cAFee, sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩) k' C' := by
  obtain ⟨_, _, hdecoded⟩ :=
    uniswapMintFeeRuntimeFactoryResultBranchesFromCall rd7781 ho32 hoSize ho132 ho1Size
      houtFeeSize
  obtain ⟨_, _, rd7825⟩ := hdecoded hzFee hout32
  exact uniswapMintFeeRuntimeFeeOffKLastNonzeroFromDecodeReturn rd7825 hfeeToZero hperm
    hkLastNonzero

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` factory-call success path returning fee-on with zero `kLast`. -/
theorem uniswapMintFeeRuntimeFactoryResultFeeOnKLastZeroReturn
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σ'' : AccountMap}
    {o o1 outFee : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 toWord sel : UInt256} {zFee : Bool}
    (rd7781 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7781⟩
      [(if zFee then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨132⟩,
        feeToSelectorWord, mintFeeFactoryWord σ'' I, ⟨0⟩, ⟨0⟩,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee)
      feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size)
    (houtFeeSize : outFee.size < UInt256.size)
    (hzFee : zFee = true)
    (hout32 : 32 ≤ outFee.size)
    (hfeeToNonzero :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
          solcAddrMask ≠
        ⟨0⟩)
    (hkLastZero : mintFeeKLastSlotWord σFee I = ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee)
      feeToStaticcallActiveWords outFee (cAFee, σFee) k' C' := by
  obtain ⟨_, _, hdecoded⟩ :=
    uniswapMintFeeRuntimeFactoryResultBranchesFromCall rd7781 ho32 hoSize ho132 ho1Size
      houtFeeSize
  obtain ⟨_, _, rd7825⟩ := hdecoded hzFee hout32
  exact uniswapMintFeeRuntimeFeeOnKLastZeroFromDecodeReturn rd7825 hfeeToNonzero hkLastZero

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` fee-on/nonzero-`kLast` slice to the checked reserve-product
multiplication routine. -/
theorem uniswapMintFeeRuntimeFeeOnKLastNonzeroMulEntry
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd7848 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7848⟩
      [kLast, feeTo, ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hkLastNonzero : kLast ≠ ⟨0⟩)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6780⟩
      [reserve1, reserve0, ⟨3737⟩, ⟨7886⟩, ⟨0⟩, kLast, feeTo, ⟨1⟩,
        reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  exact uniswapMintFeeRuntimeFeeOnKLastNonzeroMulEntryOfTail
    rd7848 hkLastNonzero hclean0 hclean1
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` fee-on/nonzero-`kLast` checked reserve-product multiply and
continuation into the first `sqrt` routine. -/
theorem uniswapMintFeeRuntimeFeeOnKLastNonzeroRootKEntry
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd6780 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6780⟩
      [reserve1, reserve0, ⟨3737⟩, ⟨7886⟩, ⟨0⟩, kLast, feeTo, ⟨1⟩,
        reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8046⟩
      [UInt256.mul reserve0 reserve1, ⟨7886⟩, ⟨0⟩, kLast, feeTo, ⟨1⟩,
        reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  exact uniswapMintFeeRuntimeFeeOnKLastNonzeroRootKEntryOfTail
    rd6780 hclean0 hclean1
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` fee-on/nonzero-`kLast` decoded branch to the first `sqrt` entry. -/
theorem uniswapMintFeeRuntimeFeeOnKLastNonzeroRootKEntryFromDecode
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd7825 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7825⟩
      [kLast, feeTo, ⟨0⟩, ⟨0⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hfeeToNonzero : UInt256.land feeTo solcAddrMask ≠ ⟨0⟩)
    (hkLastNonzero : kLast ≠ ⟨0⟩)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8046⟩
      [UInt256.mul reserve0 reserve1, ⟨7886⟩, ⟨0⟩, kLast, feeTo, ⟨1⟩,
        reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  obtain ⟨_, _, rd7848⟩ := uniswapMintFeeRuntimeFeeOnEntry rd7825 hfeeToNonzero
  obtain ⟨_, _, rd6780⟩ :=
    uniswapMintFeeRuntimeFeeOnKLastNonzeroMulEntry rd7848 hkLastNonzero hclean0 hclean1
  exact uniswapMintFeeRuntimeFeeOnKLastNonzeroRootKEntry rd6780 hclean0 hclean1


end UniswapV2Pair
