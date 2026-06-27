import Examples.BlindAuction.Reveal.Decode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 800000
namespace BlindAuction

abbrev revealScratchTimestampWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.header.timestamp

def revealScratchBiddingEndWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)

def revealScratchRevealEndWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)

def revealScratchBidsLengthSlot (I : ExecutionEnv) : UInt256 :=
  bidsBase (.address I.source)

def revealScratchBidsLengthWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (revealScratchBidsLengthSlot I) ⟨0⟩)

theorem revealScratchBiddingEndWord_accountMapEquiv {σ τ : AccountMap}
    (hστ : accountMapEquiv σ τ) (I : ExecutionEnv) :
    revealScratchBiddingEndWord σ I = revealScratchBiddingEndWord τ I := by
  exact accountMapEquiv_storage_findD hστ I.codeOwner ⟨1⟩ ⟨0⟩

theorem revealScratchRevealEndWord_accountMapEquiv {σ τ : AccountMap}
    (hστ : accountMapEquiv σ τ) (I : ExecutionEnv) :
    revealScratchRevealEndWord σ I = revealScratchRevealEndWord τ I := by
  exact accountMapEquiv_storage_findD hστ I.codeOwner ⟨2⟩ ⟨0⟩

theorem revealScratchBidsLengthWord_accountMapEquiv {σ τ : AccountMap}
    (hστ : accountMapEquiv σ τ) (I : ExecutionEnv) :
    revealScratchBidsLengthWord σ I = revealScratchBidsLengthWord τ I := by
  exact accountMapEquiv_storage_findD hστ I.codeOwner (revealScratchBidsLengthSlot I) ⟨0⟩

abbrev revealScratchSenderWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

abbrev revealScratchEmptyDecodedStack
    (I : ExecutionEnv) (valuesEnd fakesEnd secretsEnd : UInt256) : List UInt256 :=
  [⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩, blindAuctionSelWord I]

abbrev revealDecodedStack (I : ExecutionEnv)
    (valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd : UInt256) : List UInt256 :=
  [secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩,
    blindAuctionSelWord I]

theorem blindAuctionRevealDecodeArrays1806_to_413
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : Nat}
    {sel valuesLen fakesLen secretsLen : UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd : RD blindAuctionBytecode ee g s0 ⟨1806⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat ee.calldata.size, ⟨413⟩, ⟨276⟩, sel]
      mem aw rdata acc k C)
    (hvaluesGt : UInt256.gt (revealValuesOffsetWord ee) revealMaxU64 = ⟨0⟩)
    (hvaluesStart :
      UInt256.slt ((⟨4⟩ + revealValuesOffsetWord ee) + ⟨31⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨1⟩)
    (hvaluesLen :
      uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ + revealValuesOffsetWord ee).toNat 32)
        = valuesLen)
    (hvaluesLenMax : UInt256.gt valuesLen revealMaxU64 = ⟨0⟩)
    (hvaluesEnd :
      UInt256.gt (((⟨4⟩ + revealValuesOffsetWord ee) + UInt256.shiftLeft valuesLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat ee.calldata.size) = ⟨0⟩)
    (hfakesGt : UInt256.gt (revealFakesOffsetWord ee) revealMaxU64 = ⟨0⟩)
    (hfakesStart :
      UInt256.slt ((⟨4⟩ + revealFakesOffsetWord ee) + ⟨31⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨1⟩)
    (hfakesLen :
      uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ + revealFakesOffsetWord ee).toNat 32)
        = fakesLen)
    (hfakesLenMax : UInt256.gt fakesLen revealMaxU64 = ⟨0⟩)
    (hfakesEnd :
      UInt256.gt (((⟨4⟩ + revealFakesOffsetWord ee) + UInt256.shiftLeft fakesLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat ee.calldata.size) = ⟨0⟩)
    (hsecretsGt : UInt256.gt (revealSecretsOffsetWord ee) revealMaxU64 = ⟨0⟩)
    (hsecretsStart :
      UInt256.slt ((⟨4⟩ + revealSecretsOffsetWord ee) + ⟨31⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨1⟩)
    (hsecretsLen :
      uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ + revealSecretsOffsetWord ee).toNat 32)
        = secretsLen)
    (hsecretsLenMax : UInt256.gt secretsLen revealMaxU64 = ⟨0⟩)
    (hsecretsEnd :
      UInt256.gt (((⟨4⟩ + revealSecretsOffsetWord ee) + UInt256.shiftLeft secretsLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat ee.calldata.size) = ⟨0⟩) :
    ∃ k' C', RD blindAuctionBytecode ee g s0 ⟨413⟩
      [secretsLen, (⟨4⟩ + revealSecretsOffsetWord ee) + ⟨32⟩,
        fakesLen, (⟨4⟩ + revealFakesOffsetWord ee) + ⟨32⟩,
        valuesLen, (⟨4⟩ + revealValuesOffsetWord ee) + ⟨32⟩, ⟨276⟩, sel]
      mem aw rdata acc k' C' := by
  obtain ⟨_, _, rd1713v⟩ := blindAuctionRevealDecodeValuesCall1806_to_1713 rd hvaluesGt
  obtain ⟨_, _, rd1840⟩ :=
    RD.blindAuctionRevealDecodeArray1713 rd1713v hvaluesStart hvaluesLen
      (by simpa [revealMaxU64] using hvaluesLenMax) hvaluesEnd (by jump_dest) (by simp)
  have rd1841 := evm_run rd1840 with [jumpdest, swap1]
  have rd1843 := RD.swap8 rd1841 (by decide) (by simp)
  have rd1844 := evm_run rd1843 with [pop]
  have rd1845 := RD.swap6 rd1844 (by decide) (by simp)
  have rd1847 := evm_run rd1845 with [pop, pop]
  have rd1852 := evm_run rd1847 with [push1 ⟨32⟩, dup8, add, calldataload]
  have rd1861 := RD.pushConst rd1852 revealMaxU64 (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  have rd1871 := evm_run rd1861 with [
    dup2, gt, iszero, push2 ⟨1871⟩, jumpiT
      (by
        have hgt' :
            UInt256.gt
                (uInt256OfByteArray
                  (ee.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨32⟩).toNat 32))
                revealMaxU64 = ⟨0⟩ := by
          simpa [revealFakesOffsetWord, calldataWord] using hfakesGt
        rw [hgt']
        decide)
      (by jump_dest)]
  have rd1875 := evm_run rd1871 with [jumpdest, push2 ⟨1883⟩]
  have rd1876 := RD.dup10 rd1875 (by decide) (by simp)
  have rd1877 := evm_run rd1876 with [dup3]
  have rd1878 := RD.dup11 rd1877 (by decide) (by simp)
  have rd1882 := evm_run rd1878 with [add, push2 ⟨1713⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd1883⟩ :=
    RD.blindAuctionRevealDecodeArray1713 rd1882 hfakesStart hfakesLen
      (by simpa [revealMaxU64] using hfakesLenMax) hfakesEnd (by jump_dest) (by simp)
  have rd1884 := evm_run rd1883 with [jumpdest, swap1]
  have rd1885 := RD.swap6 rd1884 (by decide) (by simp)
  have rd1886 := evm_run rd1885 with [pop, swap4, pop, pop]
  have rd1895 := evm_run rd1886 with [push1 ⟨64⟩, dup8, add, calldataload]
  have rd1904 := RD.pushConst rd1895 revealMaxU64 (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  have rd1914 := evm_run rd1904 with [
    dup2, gt, iszero, push2 ⟨1914⟩, jumpiT
      (by
        have hgt' :
            UInt256.gt
                (uInt256OfByteArray
                  (ee.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨64⟩).toNat 32))
                revealMaxU64 = ⟨0⟩ := by
          simpa [revealSecretsOffsetWord, calldataWord] using hsecretsGt
        rw [hgt']
        decide)
      (by jump_dest)]
  have rd1918 := evm_run rd1914 with [jumpdest, push2 ⟨1926⟩]
  have rd1919 := RD.dup10 rd1918 (by decide) (by simp)
  have rd1920 := evm_run rd1919 with [dup3]
  have rd1921 := RD.dup11 rd1920 (by decide) (by simp)
  have rd1925 := evm_run rd1921 with [add, push2 ⟨1713⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd1926⟩ :=
    RD.blindAuctionRevealDecodeArray1713 rd1925 hsecretsStart hsecretsLen
      (by simpa [revealMaxU64] using hsecretsLenMax) hsecretsEnd (by jump_dest) (by simp)
  have rd1927 := evm_run rd1926 with [jumpdest]
  have rd1928 := RD.swap8 rd1927 (by decide) (by simp)
  have rd1929 := RD.swap11 rd1928 (by decide) (by simp)
  have rd1930 := RD.swap7 rd1929 (by decide) (by simp)
  have rd1931 := RD.swap10 rd1930 (by decide) (by simp)
  have rd1932 := evm_run rd1931 with [pop]
  have rd1933 := RD.swap5 rd1932 (by decide) (by simp)
  have rd1934 := RD.swap8 rd1933 (by decide) (by simp)
  have rd1935 := evm_run rd1934 with [pop, swap3]
  have rd1937 := RD.swap6 rd1935 (by decide) (by simp)
  have rd1939 := evm_run rd1937 with [swap4]
  have rd1940 := RD.swap5 rd1939 (by decide) (by simp)
  have rd1943 := evm_run rd1940 with [swap3, pop, pop, pop, jump (by jump_dest)]
  exact ⟨_, _, by simpa [revealDecodedStack] using rd1943⟩

theorem blindAuctionRevealDecodeArrays1806_to_887
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : Nat}
    {valuesLen fakesLen secretsLen : UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd : RD blindAuctionBytecode ee g s0 ⟨1806⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat ee.calldata.size, ⟨413⟩, ⟨276⟩, blindAuctionSelWord ee]
      mem aw rdata acc k C)
    (hvaluesGt : UInt256.gt (revealValuesOffsetWord ee) revealMaxU64 = ⟨0⟩)
    (hvaluesStart :
      UInt256.slt ((⟨4⟩ + revealValuesOffsetWord ee) + ⟨31⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨1⟩)
    (hvaluesLen :
      uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ + revealValuesOffsetWord ee).toNat 32)
        = valuesLen)
    (hvaluesLenMax : UInt256.gt valuesLen revealMaxU64 = ⟨0⟩)
    (hvaluesEnd :
      UInt256.gt (((⟨4⟩ + revealValuesOffsetWord ee) + UInt256.shiftLeft valuesLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat ee.calldata.size) = ⟨0⟩)
    (hfakesGt : UInt256.gt (revealFakesOffsetWord ee) revealMaxU64 = ⟨0⟩)
    (hfakesStart :
      UInt256.slt ((⟨4⟩ + revealFakesOffsetWord ee) + ⟨31⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨1⟩)
    (hfakesLen :
      uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ + revealFakesOffsetWord ee).toNat 32)
        = fakesLen)
    (hfakesLenMax : UInt256.gt fakesLen revealMaxU64 = ⟨0⟩)
    (hfakesEnd :
      UInt256.gt (((⟨4⟩ + revealFakesOffsetWord ee) + UInt256.shiftLeft fakesLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat ee.calldata.size) = ⟨0⟩)
    (hsecretsGt : UInt256.gt (revealSecretsOffsetWord ee) revealMaxU64 = ⟨0⟩)
    (hsecretsStart :
      UInt256.slt ((⟨4⟩ + revealSecretsOffsetWord ee) + ⟨31⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨1⟩)
    (hsecretsLen :
      uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ + revealSecretsOffsetWord ee).toNat 32)
        = secretsLen)
    (hsecretsLenMax : UInt256.gt secretsLen revealMaxU64 = ⟨0⟩)
    (hsecretsEnd :
      UInt256.gt (((⟨4⟩ + revealSecretsOffsetWord ee) + UInt256.shiftLeft secretsLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat ee.calldata.size) = ⟨0⟩) :
    ∃ k' C', RD blindAuctionBytecode ee g s0 ⟨887⟩
      (revealDecodedStack ee valuesLen ((⟨4⟩ + revealValuesOffsetWord ee) + ⟨32⟩)
        fakesLen ((⟨4⟩ + revealFakesOffsetWord ee) + ⟨32⟩)
        secretsLen ((⟨4⟩ + revealSecretsOffsetWord ee) + ⟨32⟩))
      mem aw rdata acc k' C' := by
  obtain ⟨_, _, rd413⟩ :=
    blindAuctionRevealDecodeArrays1806_to_413 rd hvaluesGt hvaluesStart hvaluesLen
      hvaluesLenMax hvaluesEnd hfakesGt hfakesStart hfakesLen hfakesLenMax hfakesEnd
      hsecretsGt hsecretsStart hsecretsLen hsecretsLenMax hsecretsEnd
  have rd887 := evm_run rd413 with [jumpdest, push2 ⟨887⟩, jump (by jump_dest)]
  exact ⟨_, _, by simpa [revealDecodedStack] using rd887⟩

noncomputable def revealScratchBidsSourceMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (UInt256.ofNat I.source.val)).write 0 solcFreePtrMem 0 32

noncomputable def revealScratchBidsHashMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (⟨4⟩ : UInt256)).write 0 (revealScratchBidsSourceMem I) 32 32

theorem revealScratchBidsSourceMem_size (I : ExecutionEnv) :
    (revealScratchBidsSourceMem I).size = 96 := by
  unfold revealScratchBidsSourceMem
  rw [write32_eq _ _ 0 (by rw [toByteArray_size]) (by omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
  norm_num

theorem revealScratchBidsSourceMem_read0 (I : ExecutionEnv) :
    (revealScratchBidsSourceMem I).readWithPadding 0 32 =
      UInt256.toByteArray (UInt256.ofNat I.source.val) := by
  unfold revealScratchBidsSourceMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [solcFreePtrMem_size]; omega),
    show (UInt256.toByteArray (UInt256.ofNat I.source.val)).extract 0 32 =
      UInt256.toByteArray (UInt256.ofNat I.source.val) from by
        apply ByteArray.ext
        rw [ByteArray.data_extract]
        exact Array.extract_eq_self_of_le (by
          change (UInt256.toByteArray (UInt256.ofNat I.source.val)).size ≤ 32
          rw [toByteArray_size])]

theorem revealScratchBidsHashMem_size (I : ExecutionEnv) :
    (revealScratchBidsHashMem I).size = 96 := by
  unfold revealScratchBidsHashMem
  rw [write32_eq _ _ 32 (by rw [toByteArray_size])
      (by rw [revealScratchBidsSourceMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, revealScratchBidsSourceMem_size,
    toByteArray_size]
  norm_num

theorem revealScratchBidsHashMem_read0 (I : ExecutionEnv) :
    (revealScratchBidsHashMem I).readWithPadding 0 32 =
      UInt256.toByteArray (UInt256.ofNat I.source.val) := by
  unfold revealScratchBidsHashMem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [revealScratchBidsSourceMem_size]; omega) (by omega)]
  unfold revealScratchBidsSourceMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [solcFreePtrMem_size]; omega),
    show (UInt256.toByteArray (UInt256.ofNat I.source.val)).extract 0 32 =
      UInt256.toByteArray (UInt256.ofNat I.source.val) from by
        apply ByteArray.ext
        rw [ByteArray.data_extract]
        exact Array.extract_eq_self_of_le (by
          change (UInt256.toByteArray (UInt256.ofNat I.source.val)).size ≤ 32
          rw [toByteArray_size])]

theorem revealScratchBidsHashMem_read32 (I : ExecutionEnv) :
    (revealScratchBidsHashMem I).readWithPadding 32 32 =
      UInt256.toByteArray (⟨4⟩ : UInt256) := by
  unfold revealScratchBidsHashMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [revealScratchBidsSourceMem_size]; omega),
    show (UInt256.toByteArray (⟨4⟩ : UInt256)).extract 0 32 =
      UInt256.toByteArray (⟨4⟩ : UInt256) from by
        apply ByteArray.ext
        rw [ByteArray.data_extract]
        exact Array.extract_eq_self_of_le (by
          change (UInt256.toByteArray (⟨4⟩ : UInt256)).size ≤ 32
          rw [toByteArray_size])]

theorem revealScratchBidsHashMem_read64 (I : ExecutionEnv) :
    (revealScratchBidsHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold revealScratchBidsHashMem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [revealScratchBidsSourceMem_size]; norm_num) (by omega)
      (by rw [revealScratchBidsSourceMem_size])]
  unfold revealScratchBidsSourceMem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [solcFreePtrMem_size]; norm_num) (by omega)
      (by rw [solcFreePtrMem_size])]
  exact solcFreePtrMem_read64

theorem revealScratchBidsHashMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (revealScratchBidsHashMem I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((revealScratchBidsHashMem I).readWithPadding
         (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
  mloadFreePtrValue (by rw [revealScratchBidsHashMem_size]; decide) (by decide)
    (revealScratchBidsHashMem_read64 I)

theorem revealScratchBidsHashMem_read0_64 (I : ExecutionEnv) :
    (revealScratchBidsHashMem I).readWithPadding 0 64 =
      UInt256.toByteArray (UInt256.ofNat I.source.val) ++
        UInt256.toByteArray (⟨4⟩ : UInt256) := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
    (by rw [revealScratchBidsHashMem_size]; omega)]
  rw [show 0 + 64 = 64 by norm_num]
  unfold revealScratchBidsHashMem
  rw [write32_eq _ _ 32 (by rw [toByteArray_size])
      (by rw [revealScratchBidsSourceMem_size]; omega)]
  have hsource :
      (revealScratchBidsSourceMem I).extract 0 32 =
        UInt256.toByteArray (UInt256.ofNat I.source.val) := by
    rw [← readWithPadding_eq_extract (revealScratchBidsSourceMem I) 0
      (by rw [revealScratchBidsSourceMem_size]; omega)]
    exact revealScratchBidsSourceMem_read0 I
  have hslot :
      (UInt256.toByteArray (⟨4⟩ : UInt256)).extract 0 32 =
        UInt256.toByteArray (⟨4⟩ : UInt256) := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray (⟨4⟩ : UInt256)).size ≤ 32
      rw [toByteArray_size])
  rw [hsource, hslot]
  rw [extract_append_left
      (UInt256.toByteArray (UInt256.ofNat I.source.val) ++
        UInt256.toByteArray (⟨4⟩ : UInt256))
      ((revealScratchBidsSourceMem I).extract (32 + 32) (revealScratchBidsSourceMem I).size)
      0 64 (by rw [ByteArray.size_append, toByteArray_size, toByteArray_size])]
  rw [extract_append_span (UInt256.toByteArray (UInt256.ofNat I.source.val))
      (UInt256.toByteArray (⟨4⟩ : UInt256)) 0 64
      (by rw [toByteArray_size]; omega)
      (by rw [toByteArray_size]; omega)]
  rw [show (UInt256.toByteArray (UInt256.ofNat I.source.val)).extract 0
      (UInt256.toByteArray (UInt256.ofNat I.source.val)).size =
        UInt256.toByteArray (UInt256.ofNat I.source.val) by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      show (UInt256.toByteArray (UInt256.ofNat I.source.val)).data.size ≤
        (UInt256.toByteArray (UInt256.ofNat I.source.val)).size
      rfl)]
  rw [show 64 - (UInt256.toByteArray (UInt256.ofNat I.source.val)).size = 32 by
    rw [toByteArray_size]]
  rw [hslot]

theorem revealScratchBidsMappingBaseKeccak (I : ExecutionEnv) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
      revealScratchBidsLengthSlot I := by
  rw [revealScratchBidsHashMem_read0_64]
  unfold revealScratchBidsLengthSlot bidsBase blindAuctionMappingSlot
  rw [keyValueToWord_address]
  exact keccakSlot_eq _

noncomputable def revealTimeRevertMem (arg errSel : UInt256) : ByteArray :=
  (UInt256.toByteArray arg).write 0 (solcReturnMem errSel) 132 32

theorem revealTimeRevertMem_size (arg errSel : UInt256) :
    (revealTimeRevertMem arg errSel).size = 164 := by
  unfold revealTimeRevertMem
  rw [write32_eq _ _ 132 (by rw [toByteArray_size])
      (by rw [solcReturnMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, solcReturnMem_size, toByteArray_size]
  rw [show ((solcReturnMem errSel).extract (132 + 32) 160).size = 0 by
    rw [ByteArray.size_extract, solcReturnMem_size]
    norm_num]
  omega

theorem revealTimeRevertMem_mload64 (arg errSel : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (revealTimeRevertMem arg errSel).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((revealTimeRevertMem arg errSel).readWithPadding
         (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
  mloadFreePtrValue (by rw [revealTimeRevertMem_size]; decide) (by decide) (by
    unfold revealTimeRevertMem
    rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
      (by rw [solcReturnMem_size]; omega) (by omega)]
    exact solcReturnMem_read64 errSel)

theorem blindAuctionRevealX_from887_tooEarly {cA σ I} {g : Sat256}
    {s0 : State} {k C : ℕ} {valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨887⟩
      (revealDecodedStack I valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (htime :
      (revealScratchTimestampWord I).toNat ≤
        (revealScratchBiddingEndWord σ I).toNat) :
    RDrev blindAuctionBytecode g s0 := by
  have rd890 := evm_run rd with [jumpdest, push1 ⟨1⟩]
  obtain ⟨_, _, rd891₀⟩ := rd890.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd891⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨891⟩
      [revealScratchBiddingEndWord σ I, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [revealScratchBiddingEndWord, revealDecodedStack] using rd891₀⟩
  have hgt : UInt256.gt (revealScratchTimestampWord I)
      (revealScratchBiddingEndWord σ I) = ⟨0⟩ :=
    ugt_zero htime
  have rd893₀ := RD.timestamp (evm_run rd891 with [dup1]) (by decide) (by evm_ov)
  have rd894₀ := evm_run rd893₀ with [gt]
  have rd894 := rd894₀
  rw [show UInt256.gt (UInt256.ofNat I.header.timestamp) (revealScratchBiddingEndWord σ I) =
      ⟨0⟩ from by simpa [revealScratchTimestampWord] using hgt] at rd894
  have rd898 := evm_run rd894 with [push2 ⟨925⟩, jumpiNT (by decide)]
  let errSel : UInt256 := UInt256.shiftLeft (⟨0x0a8d68c9⟩ : UInt256) ⟨226⟩
  have rd911 := evm_run rd898 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 ⟨0x0a8d68c9⟩, push1 ⟨226⟩, shl, dup2,
    raw mstore 6 (solcReturnMem errSel) (UInt256.ofNat 5) (by decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov)]
  have rd600 := evm_run rd911 with [
    push1 ⟨4⟩, dup2, add, dup3, swap1,
    raw mstore 3 (revealTimeRevertMem (revealScratchBiddingEndWord σ I) errSel)
      (UInt256.ofNat 6) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨36⟩, add, push2 ⟨600⟩, jump (by jump_dest)]
  have rd608 := evm_run rd600 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (revealTimeRevertMem_mload64 (revealScratchBiddingEndWord σ I) errSel)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  exact rd608.rev 0 (by decide) mem_cost (by evm_ov)

theorem blindAuctionRevealX_from887_tooLate {cA σ I} {g : Sat256}
    {s0 : State} {k C : ℕ} {valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨887⟩
      (revealDecodedStack I valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hafter :
      (revealScratchBiddingEndWord σ I).toNat < (revealScratchTimestampWord I).toNat)
    (htime :
      (revealScratchRevealEndWord σ I).toNat ≤
        (revealScratchTimestampWord I).toNat) :
    RDrev blindAuctionBytecode g s0 := by
  have rd890 := evm_run rd with [jumpdest, push1 ⟨1⟩]
  obtain ⟨_, _, rd891₀⟩ := rd890.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd891⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨891⟩
      [revealScratchBiddingEndWord σ I, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [revealScratchBiddingEndWord, revealDecodedStack] using rd891₀⟩
  have hgt : UInt256.gt (revealScratchTimestampWord I)
      (revealScratchBiddingEndWord σ I) = ⟨1⟩ :=
    ugt_one hafter
  have rd893₀ := RD.timestamp (evm_run rd891 with [dup1]) (by decide) (by evm_ov)
  have rd894₀ := evm_run rd893₀ with [gt]
  have rd894 := rd894₀
  rw [show UInt256.gt (UInt256.ofNat I.header.timestamp) (revealScratchBiddingEndWord σ I) =
      ⟨1⟩ from by simpa [revealScratchTimestampWord] using hgt] at rd894
  have rd925 := evm_run rd894 with [push2 ⟨925⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd928 := evm_run rd925 with [jumpdest, push1 ⟨2⟩]
  obtain ⟨_, _, rd929₀⟩ := rd928.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd929⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨929⟩
      [revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd,
        ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [revealScratchRevealEndWord] using rd929₀⟩
  have hlt : UInt256.lt (revealScratchTimestampWord I)
      (revealScratchRevealEndWord σ I) = ⟨0⟩ :=
    ult_zero htime
  have rd931₀ := RD.timestamp (evm_run rd929 with [dup1]) (by decide) (by evm_ov)
  have rd932₀ := evm_run rd931₀ with [lt]
  have rd932 := rd932₀
  rw [show UInt256.lt (UInt256.ofNat I.header.timestamp) (revealScratchRevealEndWord σ I) =
      ⟨0⟩ from by simpa [revealScratchTimestampWord] using hlt] at rd932
  have rd936 := evm_run rd932 with [push2 ⟨963⟩, jumpiNT (by decide)]
  let errSel : UInt256 := UInt256.shiftLeft (⟨0x348f2b41⟩ : UInt256) ⟨225⟩
  have rd949 := evm_run rd936 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 ⟨0x348f2b41⟩, push1 ⟨225⟩, shl, dup2,
    raw mstore 6 (solcReturnMem errSel) (UInt256.ofNat 5) (by decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov)]
  have rd600 := evm_run rd949 with [
    push1 ⟨4⟩, dup2, add, dup3, swap1,
    raw mstore 3 (revealTimeRevertMem (revealScratchRevealEndWord σ I) errSel)
      (UInt256.ofNat 6) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨36⟩, add, push2 ⟨600⟩, jump (by jump_dest)]
  have rd608 := evm_run rd600 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (revealTimeRevertMem_mload64 (revealScratchRevealEndWord σ I) errSel)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  exact rd608.rev 0 (by decide) mem_cost (by evm_ov)

theorem blindAuctionRevealX_from887_afterTimeGuards_empty {cA σ I} {g : Sat256}
    {s0 : State} {k C : ℕ} {valuesEnd fakesEnd secretsEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨887⟩
      (revealScratchEmptyDecodedStack I valuesEnd fakesEnd secretsEnd) solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hafter :
      (revealScratchBiddingEndWord σ I).toNat < (revealScratchTimestampWord I).toNat)
    (hbefore :
      (revealScratchTimestampWord I).toNat < (revealScratchRevealEndWord σ I).toNat) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨963⟩
      [revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd890 := evm_run rd with [jumpdest, push1 ⟨1⟩]
  obtain ⟨_, _, rd891₀⟩ := rd890.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd891⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨891⟩
      [revealScratchBiddingEndWord σ I, ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd,
        ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [revealScratchBiddingEndWord,
      revealScratchEmptyDecodedStack] using rd891₀⟩
  have hgt : UInt256.gt (revealScratchTimestampWord I) (revealScratchBiddingEndWord σ I) = ⟨1⟩ :=
    ugt_one hafter
  have rd893₀ := RD.timestamp (evm_run rd891 with [dup1]) (by decide) (by evm_ov)
  have rd894₀ := evm_run rd893₀ with [gt]
  have rd894 := rd894₀
  rw [show UInt256.gt (UInt256.ofNat I.header.timestamp) (revealScratchBiddingEndWord σ I) =
      ⟨1⟩ from by simpa [revealScratchTimestampWord] using hgt] at rd894
  have rd925 := evm_run rd894 with [push2 ⟨925⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd928 := evm_run rd925 with [jumpdest, push1 ⟨2⟩]
  obtain ⟨_, _, rd929₀⟩ := rd928.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd929⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨929⟩
      [revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [revealScratchRevealEndWord] using rd929₀⟩
  have hlt : UInt256.lt (revealScratchTimestampWord I) (revealScratchRevealEndWord σ I) = ⟨1⟩ :=
    ult_one hbefore
  have rd931₀ := RD.timestamp (evm_run rd929 with [dup1]) (by decide) (by evm_ov)
  have rd932₀ := evm_run rd931₀ with [lt]
  have rd932 := rd932₀
  rw [show UInt256.lt (UInt256.ofNat I.header.timestamp) (revealScratchRevealEndWord σ I) =
      ⟨1⟩ from by simpa [revealScratchTimestampWord] using hlt] at rd932
  exact ⟨_, _, evm_run rd932 with [push2 ⟨963⟩, jumpiT one_ne_zero_uint (by jump_dest)]⟩

theorem blindAuctionRevealX_from887_lengthMismatch_empty {cA σ I} {g : Sat256}
    {s0 : State} {k C : ℕ} {valuesEnd fakesEnd secretsEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨887⟩
      (revealScratchEmptyDecodedStack I valuesEnd fakesEnd secretsEnd) solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hafter :
      (revealScratchBiddingEndWord σ I).toNat < (revealScratchTimestampWord I).toNat)
    (hbefore :
      (revealScratchTimestampWord I).toNat < (revealScratchRevealEndWord σ I).toNat)
    (hbidsNonzero : revealScratchBidsLengthWord σ I ≠ ⟨0⟩)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    RDrev blindAuctionBytecode g s0 := by
  obtain ⟨_, _, rd963⟩ :=
    blindAuctionRevealX_from887_afterTimeGuards_empty (cA := cA) (σ := σ) (I := I)
      (g := g) (s0 := s0) rd hafter hbefore
  have rd968 := evm_run rd963 with [jumpdest, caller, push0, swap1, dup2]
  have rd969 := evm_run rd968 with [
    raw mstore 0 (revealScratchBidsSourceMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd978 := evm_run rd969 with [
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0 (revealScratchBidsHashMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1,
    raw keccak256 0 (revealScratchBidsLengthSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost hbidsHash (by decide) (by evm_ov)]
  obtain ⟨_, _, rd979₀⟩ := rd978.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd979⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨979⟩
      [revealScratchBidsLengthWord σ I, revealScratchRevealEndWord σ I,
        revealScratchBiddingEndWord σ I, ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩,
        valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [revealScratchBidsLengthWord,
      revealScratchBidsLengthSlot] using rd979₀⟩
  have heq0 : UInt256.eq (revealScratchBidsLengthWord σ I) (⟨0⟩ : UInt256) = ⟨0⟩ :=
    u256_eq_of_ne hbidsNonzero
  have rd982₀ := evm_run rd979 with [dup8, dup2, eq]
  have rd982 := rd982₀
  rw [heq0] at rd982
  have rd988 := evm_run rd982 with [push2 ⟨989⟩, jumpiNT (by decide), push0, push0]
  exact RD.rev _ rd988 (by decide)
    (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
    (by evm_ov)

theorem blindAuctionRevealX_from887_afterTimeGuards {cA σ I} {g : Sat256}
    {s0 : State} {k C : ℕ} {valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨887⟩
      (revealDecodedStack I valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hafter :
      (revealScratchBiddingEndWord σ I).toNat < (revealScratchTimestampWord I).toNat)
    (hbefore :
      (revealScratchTimestampWord I).toNat < (revealScratchRevealEndWord σ I).toNat) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨963⟩
      [revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd,
        ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd890 := evm_run rd with [jumpdest, push1 ⟨1⟩]
  obtain ⟨_, _, rd891₀⟩ := rd890.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd891⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨891⟩
      [revealScratchBiddingEndWord σ I, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [revealScratchBiddingEndWord, revealDecodedStack] using rd891₀⟩
  have hgt : UInt256.gt (revealScratchTimestampWord I) (revealScratchBiddingEndWord σ I) = ⟨1⟩ :=
    ugt_one hafter
  have rd893₀ := RD.timestamp (evm_run rd891 with [dup1]) (by decide) (by evm_ov)
  have rd894₀ := evm_run rd893₀ with [gt]
  have rd894 := rd894₀
  rw [show UInt256.gt (UInt256.ofNat I.header.timestamp) (revealScratchBiddingEndWord σ I) =
      ⟨1⟩ from by simpa [revealScratchTimestampWord] using hgt] at rd894
  have rd925 := evm_run rd894 with [push2 ⟨925⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd928 := evm_run rd925 with [jumpdest, push1 ⟨2⟩]
  obtain ⟨_, _, rd929₀⟩ := rd928.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd929⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨929⟩
      [revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd,
        ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [revealScratchRevealEndWord] using rd929₀⟩
  have hlt : UInt256.lt (revealScratchTimestampWord I) (revealScratchRevealEndWord σ I) = ⟨1⟩ :=
    ult_one hbefore
  have rd931₀ := RD.timestamp (evm_run rd929 with [dup1]) (by decide) (by evm_ov)
  have rd932₀ := evm_run rd931₀ with [lt]
  have rd932 := rd932₀
  rw [show UInt256.lt (UInt256.ofNat I.header.timestamp) (revealScratchRevealEndWord σ I) =
      ⟨1⟩ from by simpa [revealScratchTimestampWord] using hlt] at rd932
  exact ⟨_, _, evm_run rd932 with [push2 ⟨963⟩, jumpiT one_ne_zero_uint (by jump_dest)]⟩

theorem blindAuctionRevealX_from887_valuesLengthMismatch {cA σ I} {g : Sat256}
    {s0 : State} {k C : ℕ} {valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨887⟩
      (revealDecodedStack I valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hafter :
      (revealScratchBiddingEndWord σ I).toNat < (revealScratchTimestampWord I).toNat)
    (hbefore :
      (revealScratchTimestampWord I).toNat < (revealScratchRevealEndWord σ I).toNat)
    (hvaluesNe : revealScratchBidsLengthWord σ I ≠ valuesLen)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    RDrev blindAuctionBytecode g s0 := by
  obtain ⟨_, _, rd963⟩ :=
    blindAuctionRevealX_from887_afterTimeGuards (cA := cA) (σ := σ) (I := I)
      (g := g) (s0 := s0) rd hafter hbefore
  have rd968 := evm_run rd963 with [jumpdest, caller, push0, swap1, dup2]
  have rd969 := evm_run rd968 with [
    raw mstore 0 (revealScratchBidsSourceMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd978 := evm_run rd969 with [
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0 (revealScratchBidsHashMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1,
    raw keccak256 0 (revealScratchBidsLengthSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost hbidsHash (by decide) (by evm_ov)]
  obtain ⟨_, _, rd979₀⟩ := rd978.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd979⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨979⟩
      [revealScratchBidsLengthWord σ I, revealScratchRevealEndWord σ I,
        revealScratchBiddingEndWord σ I, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [revealScratchBidsLengthWord,
      revealScratchBidsLengthSlot] using rd979₀⟩
  have heq0 : UInt256.eq (revealScratchBidsLengthWord σ I) valuesLen = ⟨0⟩ :=
    u256_eq_of_ne hvaluesNe
  have rd982₀ := evm_run rd979 with [dup8, dup2, eq]
  have rd982 := rd982₀
  rw [heq0] at rd982
  have rd988 := evm_run rd982 with [push2 ⟨989⟩, jumpiNT (by decide), push0, push0]
  exact RD.rev _ rd988 (by decide)
    (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
    (by evm_ov)

theorem blindAuctionRevealX_from887_fakesLengthMismatch {cA σ I} {g : Sat256}
    {s0 : State} {k C : ℕ} {valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨887⟩
      (revealDecodedStack I valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hafter :
      (revealScratchBiddingEndWord σ I).toNat < (revealScratchTimestampWord I).toNat)
    (hbefore :
      (revealScratchTimestampWord I).toNat < (revealScratchRevealEndWord σ I).toNat)
    (hvaluesEq : revealScratchBidsLengthWord σ I = valuesLen)
    (hfakesNe : revealScratchBidsLengthWord σ I ≠ fakesLen)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    RDrev blindAuctionBytecode g s0 := by
  obtain ⟨_, _, rd963⟩ :=
    blindAuctionRevealX_from887_afterTimeGuards (cA := cA) (σ := σ) (I := I)
      (g := g) (s0 := s0) rd hafter hbefore
  have rd968 := evm_run rd963 with [jumpdest, caller, push0, swap1, dup2]
  have rd969 := evm_run rd968 with [
    raw mstore 0 (revealScratchBidsSourceMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd978 := evm_run rd969 with [
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0 (revealScratchBidsHashMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1,
    raw keccak256 0 (revealScratchBidsLengthSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost hbidsHash (by decide) (by evm_ov)]
  obtain ⟨_, _, rd979₀⟩ := rd978.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd979⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨979⟩
      [revealScratchBidsLengthWord σ I, revealScratchRevealEndWord σ I,
        revealScratchBiddingEndWord σ I, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [revealScratchBidsLengthWord,
      revealScratchBidsLengthSlot] using rd979₀⟩
  have heqValues :
      UInt256.eq (revealScratchBidsLengthWord σ I) valuesLen = ⟨1⟩ := by
    rw [← hvaluesEq]
    exact u256_eq_refl _
  have rd982₀ := evm_run rd979 with [dup8, dup2, eq]
  have rd982 := rd982₀
  rw [heqValues] at rd982
  have rd989 := evm_run rd982 with [push2 ⟨989⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have heqFakes : UInt256.eq (revealScratchBidsLengthWord σ I) fakesLen = ⟨0⟩ :=
    u256_eq_of_ne hfakesNe
  have rd993₀ := evm_run rd989 with [jumpdest, dup6, dup2, eq]
  have rd993 := rd993₀
  rw [heqFakes] at rd993
  have rd999 := evm_run rd993 with [push2 ⟨1000⟩, jumpiNT (by decide), push0, push0]
  exact RD.rev _ rd999 (by decide)
    (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
    (by evm_ov)

theorem blindAuctionRevealX_from887_secretsLengthMismatch {cA σ I} {g : Sat256}
    {s0 : State} {k C : ℕ} {valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨887⟩
      (revealDecodedStack I valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hafter :
      (revealScratchBiddingEndWord σ I).toNat < (revealScratchTimestampWord I).toNat)
    (hbefore :
      (revealScratchTimestampWord I).toNat < (revealScratchRevealEndWord σ I).toNat)
    (hvaluesEq : revealScratchBidsLengthWord σ I = valuesLen)
    (hfakesEq : revealScratchBidsLengthWord σ I = fakesLen)
    (hsecretsNe : revealScratchBidsLengthWord σ I ≠ secretsLen)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    RDrev blindAuctionBytecode g s0 := by
  obtain ⟨_, _, rd963⟩ :=
    blindAuctionRevealX_from887_afterTimeGuards (cA := cA) (σ := σ) (I := I)
      (g := g) (s0 := s0) rd hafter hbefore
  have rd968 := evm_run rd963 with [jumpdest, caller, push0, swap1, dup2]
  have rd969 := evm_run rd968 with [
    raw mstore 0 (revealScratchBidsSourceMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd978 := evm_run rd969 with [
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0 (revealScratchBidsHashMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1,
    raw keccak256 0 (revealScratchBidsLengthSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost hbidsHash (by decide) (by evm_ov)]
  obtain ⟨_, _, rd979₀⟩ := rd978.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd979⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨979⟩
      [revealScratchBidsLengthWord σ I, revealScratchRevealEndWord σ I,
        revealScratchBiddingEndWord σ I, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [revealScratchBidsLengthWord,
      revealScratchBidsLengthSlot] using rd979₀⟩
  have heqValues :
      UInt256.eq (revealScratchBidsLengthWord σ I) valuesLen = ⟨1⟩ := by
    rw [← hvaluesEq]
    exact u256_eq_refl _
  have rd982₀ := evm_run rd979 with [dup8, dup2, eq]
  have rd982 := rd982₀
  rw [heqValues] at rd982
  have rd989 := evm_run rd982 with [push2 ⟨989⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have heqFakes :
      UInt256.eq (revealScratchBidsLengthWord σ I) fakesLen = ⟨1⟩ := by
    rw [← hfakesEq]
    exact u256_eq_refl _
  have rd993₀ := evm_run rd989 with [jumpdest, dup6, dup2, eq]
  have rd993 := rd993₀
  rw [heqFakes] at rd993
  have rd1000 := evm_run rd993 with [push2 ⟨1000⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have heqSecrets : UInt256.eq (revealScratchBidsLengthWord σ I) secretsLen = ⟨0⟩ :=
    u256_eq_of_ne hsecretsNe
  have rd1004₀ := evm_run rd1000 with [jumpdest, dup4, dup2, eq]
  have rd1004 := rd1004₀
  rw [heqSecrets] at rd1004
  have rd1010 := evm_run rd1004 with [push2 ⟨1011⟩, jumpiNT (by decide), push0, push0]
  exact RD.rev _ rd1010 (by decide)
    (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
    (by evm_ov)

theorem blindAuctionRevealDecodeArrays1806_valuesLengthMismatch_reverts
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {I : ExecutionEnv}
    {g : Sat256}
    {s0 : State} {k C : Nat}
    {valuesLen fakesLen secretsLen : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1806⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨413⟩, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hvaluesGt : UInt256.gt (revealValuesOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hvaluesStart :
      UInt256.slt ((⟨4⟩ + revealValuesOffsetWord I) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hvaluesLen :
      uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + revealValuesOffsetWord I).toNat 32)
        = valuesLen)
    (hvaluesLenMax : UInt256.gt valuesLen revealMaxU64 = ⟨0⟩)
    (hvaluesEnd :
      UInt256.gt (((⟨4⟩ + revealValuesOffsetWord I) + UInt256.shiftLeft valuesLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hfakesGt : UInt256.gt (revealFakesOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hfakesStart :
      UInt256.slt ((⟨4⟩ + revealFakesOffsetWord I) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hfakesLen :
      uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + revealFakesOffsetWord I).toNat 32)
        = fakesLen)
    (hfakesLenMax : UInt256.gt fakesLen revealMaxU64 = ⟨0⟩)
    (hfakesEnd :
      UInt256.gt (((⟨4⟩ + revealFakesOffsetWord I) + UInt256.shiftLeft fakesLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hsecretsGt : UInt256.gt (revealSecretsOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hsecretsStart :
      UInt256.slt ((⟨4⟩ + revealSecretsOffsetWord I) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hsecretsLen :
      uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + revealSecretsOffsetWord I).toNat 32)
        = secretsLen)
    (hsecretsLenMax : UInt256.gt secretsLen revealMaxU64 = ⟨0⟩)
    (hsecretsEnd :
      UInt256.gt (((⟨4⟩ + revealSecretsOffsetWord I) + UInt256.shiftLeft secretsLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hafter :
      (revealScratchBiddingEndWord σ I).toNat < (revealScratchTimestampWord I).toNat)
    (hbefore :
      (revealScratchTimestampWord I).toNat < (revealScratchRevealEndWord σ I).toNat)
    (hvaluesNe : revealScratchBidsLengthWord σ I ≠ valuesLen)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    RDrev blindAuctionBytecode g s0 := by
  obtain ⟨_, _, rd887⟩ :=
    blindAuctionRevealDecodeArrays1806_to_887 (ee := I) rd hvaluesGt hvaluesStart
      hvaluesLen hvaluesLenMax hvaluesEnd hfakesGt hfakesStart hfakesLen hfakesLenMax
      hfakesEnd hsecretsGt hsecretsStart hsecretsLen hsecretsLenMax hsecretsEnd
  exact blindAuctionRevealX_from887_valuesLengthMismatch (cA := cA) (σ := σ) (I := I)
    (g := g) (s0 := s0) rd887 hafter hbefore hvaluesNe hbidsHash

theorem blindAuctionRevealDecodeArrays1806_fakesLengthMismatch_reverts
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {I : ExecutionEnv}
    {g : Sat256}
    {s0 : State} {k C : Nat}
    {valuesLen fakesLen secretsLen : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1806⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨413⟩, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hvaluesGt : UInt256.gt (revealValuesOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hvaluesStart :
      UInt256.slt ((⟨4⟩ + revealValuesOffsetWord I) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hvaluesLen :
      uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + revealValuesOffsetWord I).toNat 32)
        = valuesLen)
    (hvaluesLenMax : UInt256.gt valuesLen revealMaxU64 = ⟨0⟩)
    (hvaluesEnd :
      UInt256.gt (((⟨4⟩ + revealValuesOffsetWord I) + UInt256.shiftLeft valuesLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hfakesGt : UInt256.gt (revealFakesOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hfakesStart :
      UInt256.slt ((⟨4⟩ + revealFakesOffsetWord I) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hfakesLen :
      uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + revealFakesOffsetWord I).toNat 32)
        = fakesLen)
    (hfakesLenMax : UInt256.gt fakesLen revealMaxU64 = ⟨0⟩)
    (hfakesEnd :
      UInt256.gt (((⟨4⟩ + revealFakesOffsetWord I) + UInt256.shiftLeft fakesLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hsecretsGt : UInt256.gt (revealSecretsOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hsecretsStart :
      UInt256.slt ((⟨4⟩ + revealSecretsOffsetWord I) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hsecretsLen :
      uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + revealSecretsOffsetWord I).toNat 32)
        = secretsLen)
    (hsecretsLenMax : UInt256.gt secretsLen revealMaxU64 = ⟨0⟩)
    (hsecretsEnd :
      UInt256.gt (((⟨4⟩ + revealSecretsOffsetWord I) + UInt256.shiftLeft secretsLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hafter :
      (revealScratchBiddingEndWord σ I).toNat < (revealScratchTimestampWord I).toNat)
    (hbefore :
      (revealScratchTimestampWord I).toNat < (revealScratchRevealEndWord σ I).toNat)
    (hvaluesEq : revealScratchBidsLengthWord σ I = valuesLen)
    (hfakesNe : revealScratchBidsLengthWord σ I ≠ fakesLen)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    RDrev blindAuctionBytecode g s0 := by
  obtain ⟨_, _, rd887⟩ :=
    blindAuctionRevealDecodeArrays1806_to_887 (ee := I) rd hvaluesGt hvaluesStart
      hvaluesLen hvaluesLenMax hvaluesEnd hfakesGt hfakesStart hfakesLen hfakesLenMax
      hfakesEnd hsecretsGt hsecretsStart hsecretsLen hsecretsLenMax hsecretsEnd
  exact blindAuctionRevealX_from887_fakesLengthMismatch (cA := cA) (σ := σ) (I := I)
    (g := g) (s0 := s0) rd887 hafter hbefore hvaluesEq hfakesNe hbidsHash

theorem blindAuctionRevealDecodeArrays1806_secretsLengthMismatch_reverts
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {I : ExecutionEnv}
    {g : Sat256}
    {s0 : State} {k C : Nat}
    {valuesLen fakesLen secretsLen : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1806⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨413⟩, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hvaluesGt : UInt256.gt (revealValuesOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hvaluesStart :
      UInt256.slt ((⟨4⟩ + revealValuesOffsetWord I) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hvaluesLen :
      uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + revealValuesOffsetWord I).toNat 32)
        = valuesLen)
    (hvaluesLenMax : UInt256.gt valuesLen revealMaxU64 = ⟨0⟩)
    (hvaluesEnd :
      UInt256.gt (((⟨4⟩ + revealValuesOffsetWord I) + UInt256.shiftLeft valuesLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hfakesGt : UInt256.gt (revealFakesOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hfakesStart :
      UInt256.slt ((⟨4⟩ + revealFakesOffsetWord I) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hfakesLen :
      uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + revealFakesOffsetWord I).toNat 32)
        = fakesLen)
    (hfakesLenMax : UInt256.gt fakesLen revealMaxU64 = ⟨0⟩)
    (hfakesEnd :
      UInt256.gt (((⟨4⟩ + revealFakesOffsetWord I) + UInt256.shiftLeft fakesLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hsecretsGt : UInt256.gt (revealSecretsOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hsecretsStart :
      UInt256.slt ((⟨4⟩ + revealSecretsOffsetWord I) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hsecretsLen :
      uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + revealSecretsOffsetWord I).toNat 32)
        = secretsLen)
    (hsecretsLenMax : UInt256.gt secretsLen revealMaxU64 = ⟨0⟩)
    (hsecretsEnd :
      UInt256.gt (((⟨4⟩ + revealSecretsOffsetWord I) + UInt256.shiftLeft secretsLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hafter :
      (revealScratchBiddingEndWord σ I).toNat < (revealScratchTimestampWord I).toNat)
    (hbefore :
      (revealScratchTimestampWord I).toNat < (revealScratchRevealEndWord σ I).toNat)
    (hvaluesEq : revealScratchBidsLengthWord σ I = valuesLen)
    (hfakesEq : revealScratchBidsLengthWord σ I = fakesLen)
    (hsecretsNe : revealScratchBidsLengthWord σ I ≠ secretsLen)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    RDrev blindAuctionBytecode g s0 := by
  obtain ⟨_, _, rd887⟩ :=
    blindAuctionRevealDecodeArrays1806_to_887 (ee := I) rd hvaluesGt hvaluesStart
      hvaluesLen hvaluesLenMax hvaluesEnd hfakesGt hfakesStart hfakesLen hfakesLenMax
      hfakesEnd hsecretsGt hsecretsStart hsecretsLen hsecretsLenMax hsecretsEnd
  exact blindAuctionRevealX_from887_secretsLengthMismatch (cA := cA) (σ := σ) (I := I)
    (g := g) (s0 := s0) rd887 hafter hbefore hvaluesEq hfakesEq hsecretsNe hbidsHash

theorem blindAuctionRevealX_from963_lengthsOk_toLoopInit {cA σ I} {g : Sat256}
    {s0 : State} {k C : ℕ} {valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨963⟩
      [revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd,
        ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hvaluesEq : revealScratchBidsLengthWord σ I = valuesLen)
    (hfakesEq : revealScratchBidsLengthWord σ I = fakesLen)
    (hsecretsEq : revealScratchBidsLengthWord σ I = secretsLen)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1014⟩
      [⟨0⟩, ⟨0⟩, revealScratchBidsLengthWord σ I,
        revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd,
        ⟨276⟩, blindAuctionSelWord I]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd968 := evm_run rd with [jumpdest, caller, push0, swap1, dup2]
  have rd969 := evm_run rd968 with [
    raw mstore 0 (revealScratchBidsSourceMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd978 := evm_run rd969 with [
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0 (revealScratchBidsHashMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1,
    raw keccak256 0 (revealScratchBidsLengthSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost hbidsHash (by decide) (by evm_ov)]
  obtain ⟨_, _, rd979₀⟩ := rd978.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd979⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨979⟩
      [revealScratchBidsLengthWord σ I, revealScratchRevealEndWord σ I,
        revealScratchBiddingEndWord σ I, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [revealScratchBidsLengthWord,
      revealScratchBidsLengthSlot] using rd979₀⟩
  have heqValues :
      UInt256.eq (revealScratchBidsLengthWord σ I) valuesLen = ⟨1⟩ := by
    rw [← hvaluesEq]
    exact u256_eq_refl _
  have rd982₀ := evm_run rd979 with [dup8, dup2, eq]
  have rd982 := rd982₀
  rw [heqValues] at rd982
  have rd989 := evm_run rd982 with [push2 ⟨989⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have heqFakes :
      UInt256.eq (revealScratchBidsLengthWord σ I) fakesLen = ⟨1⟩ := by
    rw [← hfakesEq]
    exact u256_eq_refl _
  have rd993₀ := evm_run rd989 with [jumpdest, dup6, dup2, eq]
  have rd993 := rd993₀
  rw [heqFakes] at rd993
  have rd1000 := evm_run rd993 with [push2 ⟨1000⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have heqSecrets :
      UInt256.eq (revealScratchBidsLengthWord σ I) secretsLen = ⟨1⟩ := by
    rw [← hsecretsEq]
    exact u256_eq_refl _
  have rd1004₀ := evm_run rd1000 with [jumpdest, dup4, dup2, eq]
  have rd1004 := rd1004₀
  rw [heqSecrets] at rd1004
  have rd1011 := evm_run rd1004 with [push2 ⟨1011⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd1014 := evm_run rd1011 with [jumpdest, push0, dup1]
  exact ⟨_, _, rd1014⟩

theorem blindAuctionRevealX_from963_lengthsOk_zero_toCall {cA σ I} {g : Sat256}
    {s0 : State} {k C : ℕ} {valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨963⟩
      [revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd,
        ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbidsZero : revealScratchBidsLengthWord σ I = ⟨0⟩)
    (hvaluesEq : revealScratchBidsLengthWord σ I = valuesLen)
    (hfakesEq : revealScratchBidsLengthWord σ I = fakesLen)
    (hsecretsEq : revealScratchBidsLengthWord σ I = secretsLen)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    ∃ gasArg k' C', RD blindAuctionBytecode I g s0 ⟨1349⟩
      [gasArg, revealScratchSenderWord I, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, revealScratchSenderWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩,
        revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd1014⟩ :=
    blindAuctionRevealX_from963_lengthsOk_toLoopInit (cA := cA) (σ := σ) (I := I)
      (g := g) (s0 := s0) rd hvaluesEq hfakesEq hsecretsEq hbidsHash
  have hlt : UInt256.lt (⟨0⟩ : UInt256) (revealScratchBidsLengthWord σ I) = ⟨0⟩ := by
    rw [hbidsZero]
    decide
  have rd1019₀ := evm_run rd1014 with [jumpdest, dup3, dup2, lt, iszero]
  have rd1019 := rd1019₀
  rw [hlt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd1019
  have rd1331 := evm_run rd1019 with [push2 ⟨1331⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd1348₀ := evm_run rd1331 with [
    jumpdest, pop, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (revealScratchBidsHashMem_mload64 I)
      (by decide) (by evm_ov),
    push0, swap1, caller, swap1, dup4, swap1, dup4, dup2, dup2, dup2, dup6, dup8]
  obtain ⟨gasArg, rd1349⟩ := rd1348₀.gas (by decide) (by evm_ov)
  exact ⟨gasArg, _, _, by
    simpa [revealScratchSenderWord, hbidsZero, hvaluesEq, hfakesEq, hsecretsEq] using rd1349⟩

theorem blindAuctionRevealX_loopCond_taken {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1014⟩
      [i, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C)
    (hbound : i.toNat < len.toNat) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1023⟩
      [i, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k' C' := by
  have hlt : UInt256.lt i len = ⟨1⟩ := ult_one hbound
  have rd1019₀ := evm_run rd with [jumpdest, dup3, dup2, lt, iszero]
  have rd1019 := rd1019₀
  rw [hlt, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ by decide] at rd1019
  exact ⟨_, _, evm_run rd1019 with [push2 ⟨1331⟩, jumpiNT (by decide)]⟩

theorem blindAuctionRevealX_from963_lengthsOk_nonzero_toLoopBody {cA σ I}
    {g : Sat256} {s0 : State} {k C : ℕ}
    {valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨963⟩
      [revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd,
        ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbidsNonzero : revealScratchBidsLengthWord σ I ≠ ⟨0⟩)
    (hvaluesEq : revealScratchBidsLengthWord σ I = valuesLen)
    (hfakesEq : revealScratchBidsLengthWord σ I = fakesLen)
    (hsecretsEq : revealScratchBidsLengthWord σ I = secretsLen)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1023⟩
      [⟨0⟩, ⟨0⟩, revealScratchBidsLengthWord σ I,
        revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd,
        ⟨276⟩, blindAuctionSelWord I]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd1014⟩ :=
    blindAuctionRevealX_from963_lengthsOk_toLoopInit (cA := cA) (σ := σ) (I := I)
      (g := g) (s0 := s0) rd hvaluesEq hfakesEq hsecretsEq hbidsHash
  have hbound : (⟨0⟩ : UInt256).toNat < (revealScratchBidsLengthWord σ I).toNat := by
    have hneNat : (revealScratchBidsLengthWord σ I).toNat ≠ 0 := by
      intro hnat
      apply hbidsNonzero
      apply u256_inj
      change (revealScratchBidsLengthWord σ I).toNat = (⟨0⟩ : UInt256).toNat
      simpa using hnat
    simpa using Nat.pos_of_ne_zero hneNat
  exact blindAuctionRevealX_loopCond_taken rd1014 hbound

set_option maxHeartbeats 1000000 in
theorem blindAuctionRevealX_from963_empty_toCall {cA σ I} {g : Sat256}
    {s0 : State} {k C : ℕ} {valuesEnd fakesEnd secretsEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨963⟩
      [revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩,
        blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbidsZero : revealScratchBidsLengthWord σ I = ⟨0⟩)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    ∃ gasArg k' C', RD blindAuctionBytecode I g s0 ⟨1349⟩
      [gasArg, revealScratchSenderWord I, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, revealScratchSenderWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩,
        revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I, ⟨0⟩,
        secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd968 := evm_run rd with [jumpdest, caller, push0, swap1, dup2]
  have rd969 := evm_run rd968 with [
    raw mstore 0 (revealScratchBidsSourceMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd978 := evm_run rd969 with [
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0 (revealScratchBidsHashMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1,
    raw keccak256 0 (revealScratchBidsLengthSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost hbidsHash (by decide) (by evm_ov)]
  obtain ⟨_, _, rd979₀⟩ := rd978.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd979⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨979⟩
      [⟨0⟩, revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I, ⟨0⟩,
        secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    have hpc979 :
        (⟨963⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
                    UInt256.ofNat 2 +
                  UInt256.ofNat 2 +
                ⟨1⟩ +
              UInt256.ofNat 2 +
            ⟨1⟩ +
          ⟨1⟩ +
        ⟨1⟩ : UInt256) = ⟨979⟩ := by
      native_decide
    have hload0 :
        Option.option (⟨0⟩ : UInt256)
          (fun ac => Batteries.RBMap.findD ac.storage (revealScratchBidsLengthSlot I) ⟨0⟩)
          (Batteries.RBMap.find? σ I.codeOwner) = ⟨0⟩ := by
      simpa [revealScratchBidsLengthWord, revealScratchBidsLengthSlot] using hbidsZero
    exact ⟨_, _, by simpa [hpc979, hload0] using rd979₀⟩
  have rd982₀ := evm_run rd979 with [dup8, dup2, eq]
  have rd982 := rd982₀
  rw [show UInt256.eq (⟨0⟩ : UInt256) (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd982
  have rd989 := evm_run rd982 with [push2 ⟨989⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd993₀ := evm_run rd989 with [jumpdest, dup6, dup2, eq]
  have rd993 := rd993₀
  rw [show UInt256.eq (⟨0⟩ : UInt256) (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd993
  have rd1000 := evm_run rd993 with [push2 ⟨1000⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd1004₀ := evm_run rd1000 with [jumpdest, dup4, dup2, eq]
  have rd1004 := rd1004₀
  rw [show UInt256.eq (⟨0⟩ : UInt256) (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd1004
  have rd1011 := evm_run rd1004 with [push2 ⟨1011⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd1019₀ := evm_run rd1011 with [
    jumpdest, push0, dup1, jumpdest, dup3, dup2, lt, iszero]
  have rd1019 := rd1019₀
  rw [show UInt256.lt (⟨0⟩ : UInt256) (⟨0⟩ : UInt256) = ⟨0⟩ by decide,
    show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd1019
  have rd1331 := evm_run rd1019 with [push2 ⟨1331⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd1348₀ := evm_run rd1331 with [
    jumpdest, pop, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (revealScratchBidsHashMem_mload64 I)
      (by decide) (by evm_ov),
    push0, swap1, caller, swap1, dup4, swap1, dup4, dup2, dup2, dup2, dup6, dup8]
  obtain ⟨gasArg, rd1349⟩ := rd1348₀.gas (by decide) (by evm_ov)
  exact ⟨gasArg, _, _, by simpa [revealScratchSenderWord] using rd1349⟩

theorem blindAuctionRevealX_from963_empty_callMade {cA gh bl σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {valuesEnd fakesEnd secretsEnd : UInt256}
    (hdepth : I.depth.val < 1024)
    (rd : RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨963⟩
      [revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩,
        blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbidsZero : revealScratchBidsLengthWord σ I = ⟨0⟩)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA
          (initState cA gh bl σ σ₀ g A I).genesisBlockHeader
          (initState cA gh bl σ σ₀ g A I).blocks
          σ (initState cA gh bl σ σ₀ g A I).σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (revealScratchSenderWord I))
          (toExecute σ (AccountAddress.ofUInt256 (revealScratchSenderWord I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ByteArray.empty (I.depth + 1) I.header I.perm)
      ∧ o.size < UInt256.size
      ∧ RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1350⟩
          [(if z then ⟨1⟩ else ⟨0⟩), ⟨128⟩, ⟨0⟩, revealScratchSenderWord I,
            ⟨0⟩, ⟨0⟩, ⟨0⟩, revealScratchRevealEndWord σ I,
            revealScratchBiddingEndWord σ I, ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩,
            valuesEnd, ⟨276⟩, blindAuctionSelWord I]
          (revealScratchBidsHashMem I) (UInt256.ofNat 3) o (cA', σ') k' C' := by
  obtain ⟨gasArg, _, _, rd1349⟩ :=
    blindAuctionRevealX_from963_empty_toCall (cA := cA) (σ := σ) (I := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I) rd hbidsZero hbidsHash
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ, rd1350₀, hoSize⟩ :=
    rd1349.callEmptyInOut (by decide) hdepth (by evm_ov)
  have haw : UInt256.ofNat
      (MachineState.M (MachineState.M (UInt256.ofNat 3).toNat (⟨128⟩ : UInt256).toNat
        (⟨0⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) =
      (UInt256.ofNat 3) := by
    decide
  exact ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ, hoSize,
    by simpa [revealScratchSenderWord, haw] using rd1350₀⟩

set_option maxHeartbeats 1000000 in
theorem blindAuctionRevealX_from963_empty_callDepth {cA gh bl σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {valuesEnd fakesEnd secretsEnd : UInt256}
    (hdepth : I.depth = 1024)
    (rd : RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨963⟩
      [revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩,
        blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbidsZero : revealScratchBidsLengthWord σ I = ⟨0⟩)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    ∃ k' C', RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1350⟩
      [⟨0⟩, ⟨128⟩, ⟨0⟩, revealScratchSenderWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩,
        revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I, ⟨0⟩,
        secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨gasArg, _, _, rd1349⟩ :=
    blindAuctionRevealX_from963_empty_toCall (cA := cA) (σ := σ) (I := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I) rd hbidsZero hbidsHash
  obtain ⟨k', C', rd1350₀⟩ :=
    rd1349.callDepthLimitEmptyInOut (by decide) hdepth (by evm_ov)
  have haw : UInt256.ofNat
      (MachineState.M (MachineState.M (UInt256.ofNat 3).toNat (⟨128⟩ : UInt256).toNat
        (⟨0⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) =
      (UInt256.ofNat 3) := by
    decide
  exact ⟨k', C', by simpa [revealScratchSenderWord, haw] using rd1350₀⟩

theorem blindAuctionRevealX_postCallEmpty_toRequire {I} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    {z senderWord revealEnd biddingEnd valuesEnd fakesEnd secretsEnd : UInt256}
    {sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1350⟩
      [z, ⟨128⟩, ⟨0⟩, senderWord, ⟨0⟩, ⟨0⟩, ⟨0⟩, revealEnd, biddingEnd,
        ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩, sel]
      mem aw ByteArray.empty acc k C) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1405⟩
      [z, ⟨0⟩, ⟨0⟩, revealEnd, biddingEnd, ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd,
        ⟨0⟩, valuesEnd, ⟨276⟩, sel]
      mem aw ByteArray.empty acc k' C' := by
    refine ⟨_, _, evm_run rd with [
      swap3, pop, pop, pop, returndatasize, dup1, push0, dup2, eq, push2 ⟨1395⟩,
      jumpiT (by decide) (by jump_dest), jumpdest, push1 ⟨96⟩, swap2, pop,
      jumpdest, pop, pop, swap1, pop]⟩

set_option maxHeartbeats 1000000 in
theorem blindAuctionRevealX_postCallNonempty_toRequire {I} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ} {z senderWord revealEnd biddingEnd valuesEnd fakesEnd secretsEnd sel : UInt256}
    {o : ByteArray}
    (rd : RD blindAuctionBytecode I g s0 ⟨1350⟩
      [z, ⟨128⟩, ⟨0⟩, senderWord, ⟨0⟩, ⟨0⟩, ⟨0⟩, revealEnd, biddingEnd,
        ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩, sel]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) o acc k C)
    (ho0 : o.size ≠ 0) (hosz : o.size < UInt256.size) :
    ∃ mem' aw' k' C', RD blindAuctionBytecode I g s0 ⟨1405⟩
      [z, ⟨0⟩, ⟨0⟩, revealEnd, biddingEnd, ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd,
        ⟨0⟩, valuesEnd, ⟨276⟩, sel]
      mem' aw' o acc k' C' := by
  let rdsz : UInt256 := UInt256.ofNat o.size
  have hrdsz_toNat : rdsz.toNat = o.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt hosz
  have hrdsz_ne : rdsz ≠ ⟨0⟩ := by
    intro h
    have hnat : rdsz.toNat = 0 := by rw [h]; rfl
    exact ho0 (by rwa [hrdsz_toNat] at hnat)
  have heq0 : UInt256.eq rdsz (⟨0⟩ : UInt256) = ⟨0⟩ := u256_eq_of_ne hrdsz_ne
  have rd1359₀ := evm_run rd with [swap3, pop, pop, pop, returndatasize, dup1, push0, dup2, eq]
  have rd1359 := rd1359₀
  change UInt256.eq rdsz (⟨0⟩ : UInt256) = ⟨0⟩ at heq0
  rw [show UInt256.ofNat o.size = rdsz from rfl, heq0] at rd1359
  have rd1363 := evm_run rd1359 with [push2 ⟨1395⟩, jumpiNT (by decide)]
  let rounded : UInt256 := UInt256.land (UInt256.add rdsz ⟨63⟩) (UInt256.lnot ⟨31⟩)
  let mem2 : ByteArray :=
    (UInt256.toByteArray (UInt256.add ⟨128⟩ rounded)).write 0
      (revealScratchBidsHashMem I) 64 32
  have rd1381 := evm_run rd1363 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost (revealScratchBidsHashMem_mload64 I) (by decide) (by evm_ov),
    swap2, pop, push1 ⟨31⟩, not, push1 ⟨63⟩, returndatasize, add, and, dup3, add,
    push1 ⟨64⟩,
    raw mstore 0 mem2 (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  let mem3 : ByteArray := (UInt256.toByteArray rdsz).write 0 mem2 128 32
  have rd1384 := evm_run rd1381 with [
    returndatasize, dup3,
    raw mstore (Cₘ (UInt256.ofNat 5) - Cₘ (UInt256.ofNat 3))
      mem3 (UInt256.ofNat 5) (by decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        decide)
      (by rfl) (by decide) (by evm_ov)]
  have rd1390 := evm_run rd1384 with [returndatasize, push0, push1 ⟨32⟩, dup5, add]
  let copyDest : UInt256 := (⟨128⟩ : UInt256) + ⟨32⟩
  let copyLen : UInt256 := UInt256.ofNat o.size
  have hcopyDest_toNat : copyDest.toNat = 160 := by
    decide
  have hcopyLen_toNat : copyLen.toNat = o.size := by
    simpa [copyLen] using UInt256.toNat_ofNat_of_lt hosz
  let mem4 : ByteArray := o.write 0 mem3 copyDest.toNat copyLen.toNat
  have haw4 :
      UInt256.ofNat (MachineState.M (UInt256.ofNat 5).toNat copyDest.toNat copyLen.toNat) =
        SimpleAuction.withdrawReturnDataActiveWords o := by
    simp [SimpleAuction.withdrawReturnDataActiveWords, copyDest, copyLen, hcopyDest_toNat,
      hcopyLen_toNat]
  have rd1391 := RD.returndatacopy
    (Cₘ (SimpleAuction.withdrawReturnDataActiveWords o) - Cₘ (UInt256.ofNat 5))
    mem4
    (SimpleAuction.withdrawReturnDataActiveWords o)
    rd1390 (by decide)
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, hcopyLen_toNat]; omega)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, copyDest, copyLen,
        SimpleAuction.withdrawReturnDataActiveWords, hcopyDest_toNat, hcopyLen_toNat])
    (by rfl)
    haw4
    (by evm_ov)
  have rd1400 := evm_run rd1391 with [push2 ⟨1400⟩, jump (by jump_dest), jumpdest]
  exact ⟨_, _, _, _, evm_run rd1400 with [pop, pop, swap1, pop]⟩

theorem blindAuctionRevealX_postCallRequire_success_stop {I} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {revealEnd biddingEnd valuesEnd fakesEnd secretsEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1405⟩
      [⟨1⟩, ⟨0⟩, ⟨0⟩, revealEnd, biddingEnd, ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd,
        ⟨0⟩, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C) :
    RDret blindAuctionBytecode g s0 acc ByteArray.empty := by
  have rd1413 := evm_run rd with [
    dup1, push2 ⟨1413⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd276 := evm_run rd1413 with [
    jumpdest, pop, pop, pop, pop, pop, pop, pop, pop, pop, pop, pop,
    jump (by jump_dest), jumpdest]
  exact rd276.stop (by decide) (by evm_ov)

theorem blindAuctionRevealX_postCallRequire_failure_revert {I} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {revealEnd biddingEnd valuesEnd fakesEnd secretsEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1405⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, revealEnd, biddingEnd, ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd,
        ⟨0⟩, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C) :
    RDrev blindAuctionBytecode g s0 := by
  have rd1410 := evm_run rd with [
    dup1, push2 ⟨1413⟩, jumpiNT (by decide), push0, push0]
  exact RD.rev _ rd1410 (by decide)
    (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
    (by evm_ov)

theorem scratch_blindAuctionRevealX_postCallRequire_success_stop_general {I} {g : Sat256}
    {s0 : State} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {refund len revealEnd biddingEnd valuesLen valuesEnd fakesLen fakesEnd secretsLen
      secretsEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1405⟩
      [⟨1⟩, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen,
        fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C) :
    RDret blindAuctionBytecode g s0 acc ByteArray.empty := by
  have rd1413 := evm_run rd with [
    dup1, push2 ⟨1413⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd276 := evm_run rd1413 with [
    jumpdest, pop, pop, pop, pop, pop, pop, pop, pop, pop, pop, pop,
    jump (by jump_dest), jumpdest]
  exact rd276.stop (by decide) (by evm_ov)

theorem scratch_blindAuctionRevealX_postCallRequire_failure_revert_general {I} {g : Sat256}
    {s0 : State} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {refund len revealEnd biddingEnd valuesLen valuesEnd fakesLen fakesEnd secretsLen
      secretsEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1405⟩
      [⟨0⟩, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen,
        fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C) :
    RDrev blindAuctionBytecode g s0 := by
  have rd1410 := evm_run rd with [
    dup1, push2 ⟨1413⟩, jumpiNT (by decide), push0, push0]
  exact RD.rev _ rd1410 (by decide)
    (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
    (by evm_ov)

theorem blindAuctionRevealX_postCallEmpty_success_stop {I} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    {senderWord revealEnd biddingEnd valuesEnd fakesEnd secretsEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1350⟩
        [⟨1⟩, ⟨128⟩, ⟨0⟩, senderWord, ⟨0⟩, ⟨0⟩, ⟨0⟩, revealEnd, biddingEnd,
          ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩, sel]
        mem aw ByteArray.empty acc k C) :
      RDret blindAuctionBytecode g s0 acc ByteArray.empty := by
    obtain ⟨_, _, rd1405⟩ := blindAuctionRevealX_postCallEmpty_toRequire rd
    exact blindAuctionRevealX_postCallRequire_success_stop rd1405

theorem blindAuctionRevealX_postCallEmpty_failure_revert {I} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    {senderWord revealEnd biddingEnd valuesEnd fakesEnd secretsEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1350⟩
        [⟨0⟩, ⟨128⟩, ⟨0⟩, senderWord, ⟨0⟩, ⟨0⟩, ⟨0⟩, revealEnd, biddingEnd,
          ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩, sel]
        mem aw ByteArray.empty acc k C) :
      RDrev blindAuctionBytecode g s0 := by
    obtain ⟨_, _, rd1405⟩ := blindAuctionRevealX_postCallEmpty_toRequire rd
    exact blindAuctionRevealX_postCallRequire_failure_revert rd1405

theorem blindAuctionRevealBodyReverts_nonpayable {evm : EVM.State} {locals : Store}
    (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm locals
      revealTransition.body .reverted := by
  dsimp [revealTransition]
  exact bodyReverts_nonPayable h

theorem blindAuctionRevealCallvalueRequire_ok {evm : EVM.State} {locals : Store}
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecStmt blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.require (.binary .eq (.env .callvalue) (.intLit 0)))
      (.ok { contract := blindAuctionContract, locals := locals } evm) := by
  exact ExecStmt.requireTrue (evalCallvalueEq_true h)

theorem blindAuctionRevealBody_of_zero_tail {evm : EVM.State} {locals : Store} {result}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (htail : ExecFuncBody blindAuctionConfig
      { contract := blindAuctionContract, locals := locals } evm
      (List.drop 1 revealTransition.body) result) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm locals
      revealTransition.body result := by
  dsimp [ExecTransitionBody, revealTransition] at htail ⊢
  have hreq := blindAuctionRevealCallvalueRequire_ok (locals := locals) h
  cases htail with
  | execBlockOK hblk => exact ExecFuncBody.execBlockOK (ExecBlock.consNormal hreq hblk)
  | execBlockRet hblk => exact ExecFuncBody.execBlockRet (ExecBlock.consNormal hreq hblk)
  | execBlockRevert hblk => exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal hreq hblk)
  | execBlockBreak hblk => exact ExecFuncBody.execBlockBreak (ExecBlock.consNormal hreq hblk)
  | execBlockContinue hblk => exact ExecFuncBody.execBlockContinue (ExecBlock.consNormal hreq hblk)

theorem evalExpr_reveal_biddingEnd (evm : EVM.State) (locals : Store)
    (hbase : locals.get? biddingEndRef.base = none) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.storage biddingEndRef) =
        .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat)) := by
  have her : evalStorageRef blindAuctionConfig
      { contract := blindAuctionContract, locals := locals } evm biddingEndRef =
      .ok { base := "biddingEnd", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, biddingEndRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? blindAuctionContract.storage
      ({ base := "biddingEnd", steps := [] } : EvaledStorageRef) =
      some (.elem (.int uint256Int)) := by
    decide
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase) (her := her)
    (hty := hty) (hloc := blindAuctionConfig_storage_biddingEnd)]
  rw [blindAuctionStorageLocLoad_uint256]

theorem evalExpr_reveal_revealEnd (evm : EVM.State) (locals : Store)
    (hbase : locals.get? revealEndRef.base = none) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.storage revealEndRef) =
        .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)) := by
  have her : evalStorageRef blindAuctionConfig
      { contract := blindAuctionContract, locals := locals } evm revealEndRef =
      .ok { base := "revealEnd", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, revealEndRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? blindAuctionContract.storage
      ({ base := "revealEnd", steps := [] } : EvaledStorageRef) =
      some (.elem (.int uint256Int)) := by
    decide
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase) (her := her)
    (hty := hty) (hloc := blindAuctionConfig_storage_revealEnd)]
  rw [blindAuctionStorageLocLoad_uint256]

theorem evalExpr_reveal_afterBiddingEnd_true (evm : EVM.State) (locals : Store)
    (hbase : locals.get? biddingEndRef.base = none)
    (htime :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .gt now (.storage biddingEndRef)) = .ok (.bool true) := by
  simp only [evalExpr?, now, envValue, evalExpr_reveal_biddingEnd evm locals hbase, bind,
    EvalResult.bind, pure]
  simpa [evalBinaryOp?, UInt256.toNat] using htime

theorem evalExpr_reveal_afterBiddingEnd_false (evm : EVM.State) (locals : Store)
    (hbase : locals.get? biddingEndRef.base = none)
    (htime :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat ≤
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .gt now (.storage biddingEndRef)) = .ok (.bool false) := by
  simp only [evalExpr?, now, envValue, evalExpr_reveal_biddingEnd evm locals hbase, bind,
    EvalResult.bind, pure]
  simpa [evalBinaryOp?, UInt256.toNat] using htime

theorem evalExpr_reveal_beforeRevealEnd_true (evm : EVM.State) (locals : Store)
    (hbase : locals.get? revealEndRef.base = none)
    (htime :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .lt now (.storage revealEndRef)) = .ok (.bool true) := by
  simp only [evalExpr?, now, envValue, evalExpr_reveal_revealEnd evm locals hbase, bind,
    EvalResult.bind, pure]
  simpa [evalBinaryOp?, UInt256.toNat] using htime

theorem evalExpr_reveal_beforeRevealEnd_false (evm : EVM.State) (locals : Store)
    (hbase : locals.get? revealEndRef.base = none)
    (htime :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat ≤
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .lt now (.storage revealEndRef)) = .ok (.bool false) := by
  simp only [evalExpr?, now, envValue, evalExpr_reveal_revealEnd evm locals hbase, bind,
    EvalResult.bind, pure]
  simpa [evalBinaryOp?, UInt256.toNat] using htime

theorem blindAuctionRevealBodyReverts_tooEarly {evm : EVM.State} {locals : Store}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbidding : locals.get? biddingEndRef.base = none)
    (htime :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat ≤
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm locals
      revealTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  dsimp [revealTransition]
  exact (ABlock.start
    |>.requireStep (evalCallvalueEq_true hwv)
    |>.requireRevert (evalExpr_reveal_afterBiddingEnd_false evm locals hbidding htime))

theorem blindAuctionRevealBodyReverts_tooLate {evm : EVM.State} {locals : Store}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbidding : locals.get? biddingEndRef.base = none)
    (hreveal : locals.get? revealEndRef.base = none)
    (hafter :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (htime :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat ≤
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm locals
      revealTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  dsimp [revealTransition]
  exact (ABlock.start
    |>.requireStep (evalCallvalueEq_true hwv)
    |>.requireStep (evalExpr_reveal_afterBiddingEnd_true evm locals hbidding hafter)
    |>.requireRevert (evalExpr_reveal_beforeRevealEnd_false evm locals hreveal htime))

/-! ### Source-side base facts for an empty decoded reveal loop -/

def revealEmptyStore : Store :=
  (((∅ : Store).insert "values" (.array [])).insert "fakes" (.array [])).insert "secrets" (.array [])

theorem blindAuctionDecode_reveal_callargs_empty_eq {I : ExecutionEnv} {callargs : Store}
    (hdec : decodeCalldata (revealTransition.params.map Param.name)
      (transitionSignature revealTransition).paramTypes I.calldata = some callargs)
    (hvalues : callargs.get? "values" = some (.array []))
    (hfakes : callargs.get? "fakes" = some (.array []))
    (hsecrets : callargs.get? "secrets" = some (.array [])) :
    callargs = revealEmptyStore := by
  obtain ⟨values, fakes, secrets, rfl⟩ :=
    blindAuctionDecode_reveal_callargs_store_shape hdec
  have hvaluesNil : values = [] := by
    rw [store_get_ne, store_get_ne, store_get_self] at hvalues
    · cases hvalues
      rfl
    · decide
    · decide
  have hfakesNil : fakes = [] := by
    rw [store_get_ne, store_get_self] at hfakes
    · cases hfakes
      rfl
    · decide
  have hsecretsNil : secrets = [] := by
    rw [store_get_self] at hsecrets
    cases hsecrets
    rfl
  simp [revealEmptyStore, hvaluesNil, hfakesNil, hsecretsNil]

def revealLengthStore : Store :=
  revealEmptyStore.insert "length" (.int 0)

def revealRefundStore (refund : UInt256) : Store :=
  revealLengthStore.insert "refund" (.int (Int.ofNat refund.toNat))

def revealLoopStore (refund i : UInt256) : Store :=
  (revealRefundStore refund).insert "i" (.int (Int.ofNat i.toNat))

def revealCallStore (refund i : UInt256) (success : Bool) (out : ByteArray) : Store :=
  (revealLoopStore refund i).insert "success" (.bool success) |>.insert "_data" (.bytes out)

theorem revealEmptyStore_values :
    revealEmptyStore.get? "values" = some (.array []) := by
  native_decide

theorem revealEmptyStore_fakes :
    revealEmptyStore.get? "fakes" = some (.array []) := by
  native_decide

theorem revealEmptyStore_secrets :
    revealEmptyStore.get? "secrets" = some (.array []) := by
  native_decide

theorem revealEmptyStore_bids_none :
    revealEmptyStore.get? "bids" = none := by
  native_decide

theorem evalExpr_reveal_empty_values_length (evm : EVM.State) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := revealEmptyStore } evm
      (.arrayLength .localVar { base := "values" }) = .ok (.int 0) := by
  rw [evalExpr?]
  rw [revealEmptyStore_values]
  simp [readLocalPath?, EvalResult.bind, bind, pure]

theorem evalExpr_reveal_empty_fakes_length (evm : EVM.State) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := revealEmptyStore } evm
      (.arrayLength .localVar { base := "fakes" }) = .ok (.int 0) := by
  rw [evalExpr?]
  rw [revealEmptyStore_fakes]
  simp [readLocalPath?, EvalResult.bind, bind, pure]

theorem evalExpr_reveal_empty_secrets_length (evm : EVM.State) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := revealEmptyStore } evm
      (.arrayLength .localVar { base := "secrets" }) = .ok (.int 0) := by
  rw [evalExpr?]
  rw [revealEmptyStore_secrets]
  simp [readLocalPath?, EvalResult.bind, bind, pure]

theorem evalExpr_reveal_local_empty_array_length (evm : EVM.State) (locals : Store)
    (name : Ident) (h : locals.get? name = some (.array [])) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.arrayLength .localVar { base := name }) = .ok (.int 0) := by
  rw [evalExpr?]
  rw [h]
  simp [readLocalPath?, EvalResult.bind, bind, pure]

theorem evalExpr_reveal_local_array_length (evm : EVM.State) (locals : Store)
    (name : Ident) (xs : List Value) (h : locals.get? name = some (.array xs)) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.arrayLength .localVar { base := name }) = .ok (.int xs.length) := by
  rw [evalExpr?]
  rw [h]
  simp [readLocalPath?, EvalResult.bind, bind, pure]

theorem evalExpr_reveal_var_value (evm : EVM.State) (locals : Store) (name : Ident) (v : Value)
    (h : locals.get? name = some v) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.var name) = .ok v := by
  rw [evalExpr?]
  change EvalResult.ofOption .unboundVariable (locals.get? name) = .ok v
  rw [h]
  rfl

theorem evalExpr_reveal_var_int (evm : EVM.State) (locals : Store) (name : Ident) (n : Int)
    (h : locals.get? name = some (.int n)) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.var name) = .ok (.int n) := by
  exact evalExpr_reveal_var_value evm locals name (.int n) h

theorem evalExpr_reveal_local_empty_length_eq_zero_var (evm : EVM.State) (locals : Store)
    (name : Ident) (harr : locals.get? name = some (.array []))
    (hlen : locals.get? "length" = some (.int 0)) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .eq (.arrayLength .localVar { base := name }) (.var "length")) =
        .ok (.bool true) := by
  rw [evalExpr?]
  simp only [evalExpr_reveal_local_empty_array_length evm locals name harr,
    evalExpr_reveal_var_int evm locals "length" 0 hlen, EvalResult.bind, bind]
  rfl

theorem evalExpr_reveal_local_array_length_eq_var_false (evm : EVM.State) (locals : Store)
    (name : Ident) (xs : List Value) (len : UInt256)
    (harr : locals.get? name = some (.array xs))
    (hlen : locals.get? "length" = some (.int (Int.ofNat len.toNat)))
    (hne : xs.length ≠ len.toNat) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .eq (.arrayLength .localVar { base := name }) (.var "length")) =
        .ok (.bool false) := by
  rw [evalExpr?]
  simp only [evalExpr_reveal_local_array_length evm locals name xs harr,
    evalExpr_reveal_var_int evm locals "length" (Int.ofNat len.toNat) hlen,
    EvalResult.bind, bind]
  simp [evalBinaryOp?]
  have hint : (Int.ofNat xs.length == Int.ofNat len.toNat) = false := by
    simp [beq_eq_false_iff_ne, hne]
  simpa [hint] using hne

theorem evalExpr_reveal_local_array_length_eq_var_true (evm : EVM.State) (locals : Store)
    (name : Ident) (xs : List Value) (len : UInt256)
    (harr : locals.get? name = some (.array xs))
    (hlen : locals.get? "length" = some (.int (Int.ofNat len.toNat)))
    (heq : xs.length = len.toNat) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .eq (.arrayLength .localVar { base := name }) (.var "length")) =
        .ok (.bool true) := by
  rw [evalExpr?]
  simp only [evalExpr_reveal_local_array_length evm locals name xs harr,
    evalExpr_reveal_var_int evm locals "length" (Int.ofNat len.toNat) hlen,
    EvalResult.bind, bind]
  simp [evalBinaryOp?, heq]

theorem evalExpr_reveal_loop_cond_false (evm : EVM.State) (locals : Store)
    (hi : locals.get? "i" = some (.int 0))
    (hlen : locals.get? "length" = some (.int 0)) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .lt (.var "i") (.var "length")) = .ok (.bool false) := by
  rw [evalExpr?]
  simp only [evalExpr_reveal_var_int evm locals "i" 0 hi,
    evalExpr_reveal_var_int evm locals "length" 0 hlen, EvalResult.bind, bind]
  rfl

theorem evalExpr_reveal_local_array_index_any (evm : EVM.State) (locals : Store)
    (name : Ident) (xs : List Value) (idx : UInt256) (v : Value)
    (harr : locals.get? name = some (.array xs))
    (hi : locals.get? "i" = some (.int (Int.ofNat idx.toNat)))
    (hbound : idx.toNat < xs.length)
    (hlookup : lookupNth? xs idx.toNat = some v)
    (hnorm : normalizeRawBoolWord? v = .ok v) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.index (.var name) (.var "i")) = .ok v := by
  rw [evalExpr?]
  simp only [evalExpr_reveal_var_value evm locals name (.array xs) harr,
    evalExpr_reveal_var_value evm locals "i" (.int (Int.ofNat idx.toNat)) hi,
    EvalResult.bind, bind]
  unfold evalIndex?
  simp only
  rw [if_pos]
  · simp [hlookup, hnorm]
  · constructor
    · exact Int.natCast_nonneg idx.toNat
    · simpa using hbound

theorem evalExpr_reveal_sender (evm : EVM.State) (locals : Store) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      sender = .ok (.address evm.executionEnv.source) := by
  simp [sender, evalExpr?, envValue, pure]

theorem evalExpr_reveal_refund (evm : EVM.State) (locals : Store) (refund : UInt256)
    (hrefund : locals.get? "refund" = some (.int (Int.ofNat refund.toNat))) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.var "refund") = .ok (.int (Int.ofNat refund.toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption .unboundVariable (locals.get? "refund") =
    .ok (.int (Int.ofNat refund.toNat))
  rw [hrefund]
  rfl

theorem evalExpr_reveal_emptyBytes (evm : EVM.State) (locals : Store) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.newBytes (.intLit 0)) = .ok (.bytes ByteArray.empty) := by
  simp [evalExpr?, pure, bind, EvalResult.bind]
  rfl

theorem revealCallStore_success_get (refund i : UInt256) (success : Bool) (out : ByteArray) :
    (revealCallStore refund i success out).get? "success" = some (.bool success) := by
  unfold revealCallStore
  rw [store_get_ne]
  · exact store_get_self _ _ _
  · decide

theorem evalExpr_reveal_success (evm : EVM.State) (refund i : UInt256) (success : Bool)
    (out : ByteArray) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract, locals := revealCallStore refund i success out } evm
      (.var "success") = .ok (.bool success) := by
  rw [evalExpr?]
  change EvalResult.ofOption .unboundVariable
    ((revealCallStore refund i success out).get? "success") = .ok (.bool success)
  rw [revealCallStore_success_get]
  rfl

theorem evalExpr_reveal_bids_length_zero (evm : EVM.State) (locals : Store)
    (hbids : locals.get? "bids" = none)
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = ⟨0⟩) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.arrayLength .storage (bidsRef sender)) = .ok (.int 0) := by
  let er : EvaledStorageRef :=
    { base := "bids", steps := [.mindex (.address evm.executionEnv.source)] }
  have her : evalStorageRef blindAuctionConfig
      { contract := blindAuctionContract, locals := locals } evm (bidsRef sender) = .ok er := by
    simp [er, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, bidsRef, sender,
      evalExpr?, envValue, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]
  have hty : storageTypeAt? blindAuctionContract.storage er = some (.dynamicArray bidStructTy) := by
    simp [er, storageTypeAt?, blindAuctionContract, storageDecls, storageTypeStep?, bidStructTy]
  have hres :
      resolveStorageRef? blindAuctionConfig
        { contract := blindAuctionContract, locals := locals } evm (bidsRef sender) =
        .ok (er, .dynamicArray bidStructTy) :=
    resolveStorageRef?_ok hbids her hty
  rw [evalExpr?]
  simp only [hres, bind, EvalResult.bind]
  change readStorageArrayLength? blindAuctionConfig evm er (.dynamicArray bidStructTy) =
    .ok (.int 0)
  simp only [readStorageArrayLength?, er, List.cons_append, List.nil_append]
  change (match some (blindAuctionUint256Loc (bidsBase (.address evm.executionEnv.source))) with
    | some lenLoc =>
        match storageLocLoad evm lenLoc with
        | Value.int n => pure (Value.int n)
        | _ => EvalResult.error .storageError
    | none => EvalResult.error .storageError) = EvalResult.ok (Value.int 0)
  change (match storageLocLoad evm (blindAuctionUint256Loc (bidsBase (.address evm.executionEnv.source))) with
    | Value.int n => pure (Value.int n)
    | _ => EvalResult.error .storageError) = EvalResult.ok (Value.int 0)
  rw [blindAuctionStorageLocLoad_uint256, hlen]
  rfl

theorem evalExpr_reveal_bids_length_any (evm : EVM.State) (locals : Store) (len : UInt256)
    (hbids : locals.get? "bids" = none)
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.arrayLength .storage (bidsRef sender)) = .ok (.int (Int.ofNat len.toNat)) := by
  let er : EvaledStorageRef :=
    { base := "bids", steps := [.mindex (.address evm.executionEnv.source)] }
  have her : evalStorageRef blindAuctionConfig
      { contract := blindAuctionContract, locals := locals } evm (bidsRef sender) = .ok er := by
    simp [er, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, bidsRef, sender,
      evalExpr?, envValue, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]
  have hty : storageTypeAt? blindAuctionContract.storage er = some (.dynamicArray bidStructTy) := by
    simp [er, storageTypeAt?, blindAuctionContract, storageDecls, storageTypeStep?, bidStructTy]
  have hres :
      resolveStorageRef? blindAuctionConfig
        { contract := blindAuctionContract, locals := locals } evm (bidsRef sender) =
        .ok (er, .dynamicArray bidStructTy) :=
    resolveStorageRef?_ok hbids her hty
  rw [evalExpr?]
  simp only [hres, bind, EvalResult.bind]
  change readStorageArrayLength? blindAuctionConfig evm er (.dynamicArray bidStructTy) =
    .ok (.int (Int.ofNat len.toNat))
  simp only [readStorageArrayLength?, er, List.cons_append, List.nil_append]
  change (match some (blindAuctionUint256Loc (bidsBase (.address evm.executionEnv.source))) with
    | some lenLoc =>
        match storageLocLoad evm lenLoc with
        | Value.int n => pure (Value.int n)
        | _ => EvalResult.error .storageError
    | none => EvalResult.error .storageError) = EvalResult.ok (Value.int (Int.ofNat len.toNat))
  change (match storageLocLoad evm (blindAuctionUint256Loc (bidsBase (.address evm.executionEnv.source))) with
    | Value.int n => pure (Value.int n)
    | _ => EvalResult.error .storageError) = EvalResult.ok (Value.int (Int.ofNat len.toNat))
  rw [blindAuctionStorageLocLoad_uint256, hlen]
  rfl

theorem blindAuctionRevealBodyReturns_empty_callSuccess
    (evm evm' : EVM.State) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hafter :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbefore :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = ⟨0⟩)
    (hcall :
      callViaEVM evm (EVM.address evm.executionEnv.source) 0 ByteArray.empty
        (true, evm', out)) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm revealEmptyStore
      revealTransition.body
      (.returned { contract := blindAuctionContract, locals := revealCallStore ⟨0⟩ ⟨0⟩ true out }
        evm' none) := by
  refine ExecFuncBody.execBlockOK ?_
  unfold revealTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_afterBiddingEnd_true evm revealEmptyStore (by native_decide) hafter)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_beforeRevealEnd_true evm revealEmptyStore (by native_decide) hbefore)) ?_
  have hlengthEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := revealEmptyStore }
        evm (.arrayLength .storage (bidsRef sender)) = .ok (.int 0) := by
    exact evalExpr_reveal_bids_length_zero evm revealEmptyStore revealEmptyStore_bids_none hlen
  refine ExecBlock.consNormal (ExecStmt.letDecl hlengthEval) ?_
  change ExecBlock blindAuctionConfig
    { contract := blindAuctionContract, locals := revealLengthStore } evm
    [ .require (.binary .eq (.arrayLength .localVar { base := "values" }) (.var "length")),
      .require (.binary .eq (.arrayLength .localVar { base := "fakes" }) (.var "length")),
      .require (.binary .eq (.arrayLength .localVar { base := "secrets" }) (.var "length")),
      .letDecl "refund" (some uint256) (.intLit 0),
      .for [ .letDecl "i" (some uint256) (.intLit 0) ]
        (.binary .lt (.var "i") (.var "length"))
        [ .assign .localVar { base := "i" } (.binary .add (.var "i") (.intLit 1)) ]
        [ .letStorage "bidToCheck" (bidElemRef sender (.var "i")),
          .letDecl "value" (some uint256) (.index (.var "values") (.var "i")),
          .letDecl "fake" (some boolTy) (.index (.var "fakes") (.var "i")),
          .letDecl "secret" (some bytes32) (.index (.var "secrets") (.var "i")),
          .ite
            (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
              (.keccak256 (.abiEncodePacked
                [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
            [.continue] [],
          .assign .localVar { base := "refund" }
            (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
          .ite
            (.binary .and (.unary .not (.var "fake"))
              (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
            [ .internalCall "placeBid" [sender, .var "value"] "ok",
              .ite (.var "ok")
                [ .assign .localVar { base := "refund" }
                    (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
          .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ],
      .lowLevelCall sender (.var "refund") (.newBytes (.intLit 0)) "success" "_data",
      .require (.var "success") ]
    (.ok { contract := blindAuctionContract, locals := revealCallStore ⟨0⟩ ⟨0⟩ true out }
      evm')
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_empty_length_eq_zero_var evm revealLengthStore "values"
        (by native_decide) (by native_decide))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_empty_length_eq_zero_var evm revealLengthStore "fakes"
        (by native_decide) (by native_decide))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_empty_length_eq_zero_var evm revealLengthStore "secrets"
        (by native_decide) (by native_decide))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (value := .int 0) (by simp [evalExpr?, pure])) ?_
  change ExecBlock blindAuctionConfig
    { contract := blindAuctionContract, locals := revealRefundStore ⟨0⟩ } evm
    [ .for [ .letDecl "i" (some uint256) (.intLit 0) ]
        (.binary .lt (.var "i") (.var "length"))
        [ .assign .localVar { base := "i" } (.binary .add (.var "i") (.intLit 1)) ]
        [ .letStorage "bidToCheck" (bidElemRef sender (.var "i")),
          .letDecl "value" (some uint256) (.index (.var "values") (.var "i")),
          .letDecl "fake" (some boolTy) (.index (.var "fakes") (.var "i")),
          .letDecl "secret" (some bytes32) (.index (.var "secrets") (.var "i")),
          .ite
            (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
              (.keccak256 (.abiEncodePacked
                [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
            [.continue] [],
          .assign .localVar { base := "refund" }
            (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
          .ite
            (.binary .and (.unary .not (.var "fake"))
              (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
            [ .internalCall "placeBid" [sender, .var "value"] "ok",
              .ite (.var "ok")
                [ .assign .localVar { base := "refund" }
                    (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
          .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ],
      .lowLevelCall sender (.var "refund") (.newBytes (.intLit 0)) "success" "_data",
      .require (.var "success") ]
    (.ok { contract := blindAuctionContract, locals := revealCallStore ⟨0⟩ ⟨0⟩ true out }
      evm')
  have hfor :
      ExecStmt blindAuctionConfig
        { contract := blindAuctionContract, locals := revealRefundStore ⟨0⟩ } evm
        (.for [ .letDecl "i" (some uint256) (.intLit 0) ]
          (.binary .lt (.var "i") (.var "length"))
          [ .assign .localVar { base := "i" } (.binary .add (.var "i") (.intLit 1)) ]
          [ .letStorage "bidToCheck" (bidElemRef sender (.var "i")),
            .letDecl "value" (some uint256) (.index (.var "values") (.var "i")),
            .letDecl "fake" (some boolTy) (.index (.var "fakes") (.var "i")),
            .letDecl "secret" (some bytes32) (.index (.var "secrets") (.var "i")),
            .ite
              (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
                (.keccak256 (.abiEncodePacked
                  [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
              [.continue] [],
            .assign .localVar { base := "refund" }
              (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
            .ite
              (.binary .and (.unary .not (.var "fake"))
                (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
              [ .internalCall "placeBid" [sender, .var "value"] "ok",
                .ite (.var "ok")
                  [ .assign .localVar { base := "refund" }
                      (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
            .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ])
        (.ok { contract := blindAuctionContract, locals := revealLoopStore ⟨0⟩ ⟨0⟩ } evm) := by
    have hinit :
        ExecBlock blindAuctionConfig
          { contract := blindAuctionContract, locals := revealRefundStore ⟨0⟩ } evm
          [ .letDecl "i" (some uint256) (.intLit 0) ]
          (.ok { contract := blindAuctionContract, locals := revealLoopStore ⟨0⟩ ⟨0⟩ } evm) := by
      refine ExecBlock.consNormal
        (ExecStmt.letDecl (value := .int 0) (by simp [evalExpr?, pure])) ?_
      exact ExecBlock.nil
    have hloop :
        ExecForLoop blindAuctionConfig
          { contract := blindAuctionContract, locals := revealLoopStore ⟨0⟩ ⟨0⟩ } evm
          (.binary .lt (.var "i") (.var "length"))
          [ .assign .localVar { base := "i" } (.binary .add (.var "i") (.intLit 1)) ]
          [ .letStorage "bidToCheck" (bidElemRef sender (.var "i")),
            .letDecl "value" (some uint256) (.index (.var "values") (.var "i")),
            .letDecl "fake" (some boolTy) (.index (.var "fakes") (.var "i")),
            .letDecl "secret" (some bytes32) (.index (.var "secrets") (.var "i")),
            .ite
              (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
                (.keccak256 (.abiEncodePacked
                  [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
              [.continue] [],
            .assign .localVar { base := "refund" }
              (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
            .ite
              (.binary .and (.unary .not (.var "fake"))
                (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
              [ .internalCall "placeBid" [sender, .var "value"] "ok",
                .ite (.var "ok")
                  [ .assign .localVar { base := "refund" }
                      (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
            .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
          (.ok { contract := blindAuctionContract, locals := revealLoopStore ⟨0⟩ ⟨0⟩ } evm) := by
      exact ExecForLoop.falseDone
        (evalExpr_reveal_loop_cond_false evm (revealLoopStore ⟨0⟩ ⟨0⟩)
          (by native_decide) (by native_decide))
    exact ExecStmt.for hinit hloop
  refine ExecBlock.consNormal hfor ?_
  refine ExecBlock.consNormal
    (ExecStmt.lowLevelCallSuccess
      (evalExpr_reveal_sender evm (revealLoopStore ⟨0⟩ ⟨0⟩))
      (evalExpr_reveal_refund evm (revealLoopStore ⟨0⟩ ⟨0⟩) ⟨0⟩ (by native_decide))
      (evalExpr_reveal_emptyBytes evm (revealLoopStore ⟨0⟩ ⟨0⟩))
      hcall) ?_
  exact ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_reveal_success evm' ⟨0⟩ ⟨0⟩ true out))
    ExecBlock.nil

theorem blindAuctionRevealBodyReverts_empty_callFailure
    (evm evm' : EVM.State) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hafter :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbefore :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = ⟨0⟩)
    (hcall :
      callViaEVM evm (EVM.address evm.executionEnv.source) 0 ByteArray.empty
        (false, evm', out)) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm revealEmptyStore
      revealTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  unfold revealTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_afterBiddingEnd_true evm revealEmptyStore (by native_decide) hafter)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_beforeRevealEnd_true evm revealEmptyStore (by native_decide) hbefore)) ?_
  have hlengthEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := revealEmptyStore }
        evm (.arrayLength .storage (bidsRef sender)) = .ok (.int 0) := by
    exact evalExpr_reveal_bids_length_zero evm revealEmptyStore revealEmptyStore_bids_none hlen
  refine ExecBlock.consNormal (ExecStmt.letDecl hlengthEval) ?_
  change ExecBlock blindAuctionConfig
    { contract := blindAuctionContract, locals := revealLengthStore } evm
    (List.drop 4 revealTransition.body) .reverted
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_empty_length_eq_zero_var evm revealLengthStore "values"
        (by native_decide) (by native_decide))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_empty_length_eq_zero_var evm revealLengthStore "fakes"
        (by native_decide) (by native_decide))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_empty_length_eq_zero_var evm revealLengthStore "secrets"
        (by native_decide) (by native_decide))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (value := .int 0) (by simp [evalExpr?, pure])) ?_
  change ExecBlock blindAuctionConfig
    { contract := blindAuctionContract, locals := revealRefundStore ⟨0⟩ } evm
    (List.drop 8 revealTransition.body) .reverted
  have hfor :
      ExecStmt blindAuctionConfig
        { contract := blindAuctionContract, locals := revealRefundStore ⟨0⟩ } evm
        (.for [ .letDecl "i" (some uint256) (.intLit 0) ]
          (.binary .lt (.var "i") (.var "length"))
          [ .assign .localVar { base := "i" } (.binary .add (.var "i") (.intLit 1)) ]
          [ .letStorage "bidToCheck" (bidElemRef sender (.var "i")),
            .letDecl "value" (some uint256) (.index (.var "values") (.var "i")),
            .letDecl "fake" (some boolTy) (.index (.var "fakes") (.var "i")),
            .letDecl "secret" (some bytes32) (.index (.var "secrets") (.var "i")),
            .ite
              (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
                (.keccak256 (.abiEncodePacked
                  [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
              [.continue] [],
            .assign .localVar { base := "refund" }
              (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
            .ite
              (.binary .and (.unary .not (.var "fake"))
                (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
              [ .internalCall "placeBid" [sender, .var "value"] "ok",
                .ite (.var "ok")
                  [ .assign .localVar { base := "refund" }
                      (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
            .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ])
        (.ok { contract := blindAuctionContract, locals := revealLoopStore ⟨0⟩ ⟨0⟩ } evm) := by
    have hinit :
        ExecBlock blindAuctionConfig
          { contract := blindAuctionContract, locals := revealRefundStore ⟨0⟩ } evm
          [ .letDecl "i" (some uint256) (.intLit 0) ]
          (.ok { contract := blindAuctionContract, locals := revealLoopStore ⟨0⟩ ⟨0⟩ } evm) := by
      refine ExecBlock.consNormal
        (ExecStmt.letDecl (value := .int 0) (by simp [evalExpr?, pure])) ?_
      exact ExecBlock.nil
    have hloop :
        ExecForLoop blindAuctionConfig
          { contract := blindAuctionContract, locals := revealLoopStore ⟨0⟩ ⟨0⟩ } evm
          (.binary .lt (.var "i") (.var "length"))
          [ .assign .localVar { base := "i" } (.binary .add (.var "i") (.intLit 1)) ]
          [ .letStorage "bidToCheck" (bidElemRef sender (.var "i")),
            .letDecl "value" (some uint256) (.index (.var "values") (.var "i")),
            .letDecl "fake" (some boolTy) (.index (.var "fakes") (.var "i")),
            .letDecl "secret" (some bytes32) (.index (.var "secrets") (.var "i")),
            .ite
              (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
                (.keccak256 (.abiEncodePacked
                  [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
              [.continue] [],
            .assign .localVar { base := "refund" }
              (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
            .ite
              (.binary .and (.unary .not (.var "fake"))
                (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
              [ .internalCall "placeBid" [sender, .var "value"] "ok",
                .ite (.var "ok")
                  [ .assign .localVar { base := "refund" }
                      (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
            .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
          (.ok { contract := blindAuctionContract, locals := revealLoopStore ⟨0⟩ ⟨0⟩ } evm) := by
      exact ExecForLoop.falseDone
        (evalExpr_reveal_loop_cond_false evm (revealLoopStore ⟨0⟩ ⟨0⟩)
          (by native_decide) (by native_decide))
    exact ExecStmt.for hinit hloop
  refine ExecBlock.consNormal hfor ?_
  refine ExecBlock.consNormal
    (ExecStmt.lowLevelCallFailure
      (evalExpr_reveal_sender evm (revealLoopStore ⟨0⟩ ⟨0⟩))
      (evalExpr_reveal_refund evm (revealLoopStore ⟨0⟩ ⟨0⟩) ⟨0⟩ (by native_decide))
      (evalExpr_reveal_emptyBytes evm (revealLoopStore ⟨0⟩ ⟨0⟩))
      hcall) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_reveal_success evm' ⟨0⟩ ⟨0⟩ false out))

theorem blindAuctionRevealBodyReverts_valuesLengthMismatch (evm : EVM.State)
    (callargs : Store) (values : List Value) (len : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbidding : callargs.get? biddingEndRef.base = none)
    (hreveal : callargs.get? revealEndRef.base = none)
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hafter :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbefore :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hne : values.length ≠ len.toNat) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm callargs
      revealTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  unfold revealTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_afterBiddingEnd_true evm callargs hbidding hafter)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_beforeRevealEnd_true evm callargs hreveal hbefore)) ?_
  have hlengthEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := callargs }
        evm (.arrayLength .storage (bidsRef sender)) = .ok (.int (Int.ofNat len.toNat)) := by
    exact evalExpr_reveal_bids_length_any evm callargs len hbids hlen
  refine ExecBlock.consNormal (ExecStmt.letDecl hlengthEval) ?_
  change ExecBlock blindAuctionConfig
    { contract := blindAuctionContract,
      locals := callargs.insert "length" (.int (Int.ofNat len.toNat)) } evm
    (List.drop 4 revealTransition.body) .reverted
  refine ExecBlock.consRevert ?_
  refine ExecStmt.requireFalse ?_
  apply evalExpr_reveal_local_array_length_eq_var_false
  · rw [store_get_ne]
    · exact hvalues
    · decide
  · rw [store_get_self]
  · exact hne

theorem blindAuctionRevealBodyReverts_fakesLengthMismatch (evm : EVM.State)
    (callargs : Store) (values fakes : List Value) (len : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbidding : callargs.get? biddingEndRef.base = none)
    (hreveal : callargs.get? revealEndRef.base = none)
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hafter :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbefore :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hvaluesLen : values.length = len.toNat)
    (hfakesNe : fakes.length ≠ len.toNat) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm callargs
      revealTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  unfold revealTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_afterBiddingEnd_true evm callargs hbidding hafter)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_beforeRevealEnd_true evm callargs hreveal hbefore)) ?_
  have hlengthEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := callargs } evm
        (.arrayLength .storage (bidsRef sender)) = .ok (.int (Int.ofNat len.toNat)) := by
    exact evalExpr_reveal_bids_length_any evm callargs len hbids hlen
  refine ExecBlock.consNormal (ExecStmt.letDecl hlengthEval) ?_
  change ExecBlock blindAuctionConfig
    { contract := blindAuctionContract,
      locals := callargs.insert "length" (.int (Int.ofNat len.toNat)) } evm
    (List.drop 4 revealTransition.body) .reverted
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_array_length_eq_var_true evm
        (callargs.insert "length" (.int (Int.ofNat len.toNat))) "values" values len
        (by
          rw [store_get_ne]
          · exact hvalues
          · decide)
        (by rw [store_get_self]) hvaluesLen)) ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.requireFalse ?_
  apply evalExpr_reveal_local_array_length_eq_var_false
  · rw [store_get_ne]
    · exact hfakes
    · decide
  · rw [store_get_self]
  · exact hfakesNe

theorem blindAuctionRevealBodyReverts_secretsLengthMismatch (evm : EVM.State)
    (callargs : Store) (values fakes secrets : List Value) (len : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbidding : callargs.get? biddingEndRef.base = none)
    (hreveal : callargs.get? revealEndRef.base = none)
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hsecrets : callargs.get? "secrets" = some (.array secrets))
    (hafter :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbefore :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hvaluesLen : values.length = len.toNat)
    (hfakesLen : fakes.length = len.toNat)
    (hsecretsNe : secrets.length ≠ len.toNat) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm callargs
      revealTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  unfold revealTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_afterBiddingEnd_true evm callargs hbidding hafter)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_beforeRevealEnd_true evm callargs hreveal hbefore)) ?_
  have hlengthEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := callargs } evm
        (.arrayLength .storage (bidsRef sender)) = .ok (.int (Int.ofNat len.toNat)) := by
    exact evalExpr_reveal_bids_length_any evm callargs len hbids hlen
  refine ExecBlock.consNormal (ExecStmt.letDecl hlengthEval) ?_
  change ExecBlock blindAuctionConfig
    { contract := blindAuctionContract,
      locals := callargs.insert "length" (.int (Int.ofNat len.toNat)) } evm
    (List.drop 4 revealTransition.body) .reverted
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_array_length_eq_var_true evm
        (callargs.insert "length" (.int (Int.ofNat len.toNat))) "values" values len
        (by
          rw [store_get_ne]
          · exact hvalues
          · decide)
        (by rw [store_get_self]) hvaluesLen)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_array_length_eq_var_true evm
        (callargs.insert "length" (.int (Int.ofNat len.toNat))) "fakes" fakes len
        (by
          rw [store_get_ne]
          · exact hfakes
          · decide)
        (by rw [store_get_self]) hfakesLen)) ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.requireFalse ?_
  apply evalExpr_reveal_local_array_length_eq_var_false
  · rw [store_get_ne]
    · exact hsecrets
    · decide
  · rw [store_get_self]
  · exact hsecretsNe

theorem blindAuctionRevealBodyReverts_decoded_lengthMismatch
    (evm : EVM.State) {I : ExecutionEnv} {callargs : Store} {len : UInt256}
    {values fakes secrets : List Value}
    (hdec : decodeCalldata (revealTransition.params.map Param.name)
      (transitionSignature revealTransition).paramTypes I.calldata = some callargs)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hsecrets : callargs.get? "secrets" = some (.array secrets))
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hafter :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbefore :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hmismatch :
      values.length ≠ len.toNat ∨ fakes.length ≠ len.toNat ∨
        secrets.length ≠ len.toNat) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm callargs
      revealTransition.body .reverted := by
  have hbids : callargs.get? "bids" = none :=
    blindAuctionDecode_reveal_callargs_absent hdec (by decide) (by decide) (by decide)
  have hbidding : callargs.get? biddingEndRef.base = none :=
    blindAuctionDecode_reveal_callargs_absent hdec (by decide) (by decide) (by decide)
  have hreveal : callargs.get? revealEndRef.base = none :=
    blindAuctionDecode_reveal_callargs_absent hdec (by decide) (by decide) (by decide)
  by_cases hvaluesEq : values.length = len.toNat
  · by_cases hfakesEq : fakes.length = len.toNat
    · have hsecretsNe : secrets.length ≠ len.toNat := by
        rcases hmismatch with hvaluesNe | htail
        · exact False.elim (hvaluesNe hvaluesEq)
        · rcases htail with hfakesNe | hsecretsNe
          · exact False.elim (hfakesNe hfakesEq)
          · exact hsecretsNe
      exact blindAuctionRevealBodyReverts_secretsLengthMismatch evm callargs values fakes
        secrets len hwv hbidding hreveal hbids hvalues hfakes hsecrets hafter hbefore hlen
        hvaluesEq hfakesEq hsecretsNe
    · exact blindAuctionRevealBodyReverts_fakesLengthMismatch evm callargs values fakes len
        hwv hbidding hreveal hbids hvalues hfakes hafter hbefore hlen hvaluesEq hfakesEq
  · exact blindAuctionRevealBodyReverts_valuesLengthMismatch evm callargs values len hwv
      hbidding hreveal hbids hvalues hafter hbefore hlen hvaluesEq

end BlindAuction

/-! ### Ported reveal nonempty loop execution helpers -/



namespace BlindAuction

theorem scratch_blindAuctionRevealX_postCallEmpty_toRequire_general {I} {g : Sat256}
    {s0 : State} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    {z senderWord refund len revealEnd biddingEnd valuesLen valuesEnd fakesLen fakesEnd
      secretsLen secretsEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1350⟩
      [z, ⟨128⟩, refund, senderWord, ⟨0⟩, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw ByteArray.empty acc k C) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1405⟩
      [z, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw ByteArray.empty acc k' C' := by
  refine ⟨_, _, evm_run rd with [
    swap3, pop, pop, pop, returndatasize, dup1, push0, dup2, eq, push2 ⟨1395⟩,
    jumpiT (by decide) (by jump_dest), jumpdest, push1 ⟨96⟩, swap2, pop,
    jumpdest, pop, pop, swap1, pop]⟩

theorem scratch_blindAuctionRevealX_postCallEmpty_toRequire_freePtr {I} {g : Sat256}
    {s0 : State} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    {z senderWord refund len freePtr revealEnd biddingEnd valuesLen valuesEnd fakesLen fakesEnd
      secretsLen secretsEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1350⟩
      [z, freePtr, refund, senderWord, ⟨0⟩, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw ByteArray.empty acc k C) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1405⟩
      [z, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw ByteArray.empty acc k' C' := by
  refine ⟨_, _, evm_run rd with [
    swap3, pop, pop, pop, returndatasize, dup1, push0, dup2, eq, push2 ⟨1395⟩,
    jumpiT (by decide) (by jump_dest), jumpdest, push1 ⟨96⟩, swap2, pop,
    jumpdest, pop, pop, swap1, pop]⟩

set_option maxHeartbeats 1000000 in
theorem scratch_blindAuctionRevealX_postCallNonempty_toRequire_general {I} {g : Sat256}
    {s0 : State} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ} {z senderWord refund len revealEnd biddingEnd valuesLen valuesEnd fakesLen
      fakesEnd secretsLen secretsEnd sel : UInt256}
    {o : ByteArray}
    (rd : RD blindAuctionBytecode I g s0 ⟨1350⟩
      [z, ⟨128⟩, refund, senderWord, ⟨0⟩, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) o acc k C)
    (ho0 : o.size ≠ 0) (hosz : o.size < UInt256.size) :
    ∃ mem' aw' k' C', RD blindAuctionBytecode I g s0 ⟨1405⟩
      [z, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, sel]
      mem' aw' o acc k' C' := by
  let rdsz : UInt256 := UInt256.ofNat o.size
  have hrdsz_toNat : rdsz.toNat = o.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt hosz
  have hrdsz_ne : rdsz ≠ ⟨0⟩ := by
    intro h
    have hnat : rdsz.toNat = 0 := by rw [h]; rfl
    exact ho0 (by rwa [hrdsz_toNat] at hnat)
  have heq0 : UInt256.eq rdsz (⟨0⟩ : UInt256) = ⟨0⟩ := u256_eq_of_ne hrdsz_ne
  have rd1359₀ := evm_run rd with [swap3, pop, pop, pop, returndatasize, dup1, push0, dup2, eq]
  have rd1359 := rd1359₀
  change UInt256.eq rdsz (⟨0⟩ : UInt256) = ⟨0⟩ at heq0
  rw [show UInt256.ofNat o.size = rdsz from rfl, heq0] at rd1359
  have rd1363 := evm_run rd1359 with [push2 ⟨1395⟩, jumpiNT (by decide)]
  let rounded : UInt256 := UInt256.land (UInt256.add rdsz ⟨63⟩) (UInt256.lnot ⟨31⟩)
  let mem2 : ByteArray :=
    (UInt256.toByteArray (UInt256.add ⟨128⟩ rounded)).write 0
      (revealScratchBidsHashMem I) 64 32
  have rd1381 := evm_run rd1363 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost (revealScratchBidsHashMem_mload64 I) (by decide) (by evm_ov),
    swap2, pop, push1 ⟨31⟩, not, push1 ⟨63⟩, returndatasize, add, and, dup3, add,
    push1 ⟨64⟩,
    raw mstore 0 mem2 (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  let mem3 : ByteArray := (UInt256.toByteArray rdsz).write 0 mem2 128 32
  have rd1384 := evm_run rd1381 with [
    returndatasize, dup3,
    raw mstore (Cₘ (UInt256.ofNat 5) - Cₘ (UInt256.ofNat 3))
      mem3 (UInt256.ofNat 5) (by decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        decide)
      (by rfl) (by decide) (by evm_ov)]
  have rd1390 := evm_run rd1384 with [returndatasize, push0, push1 ⟨32⟩, dup5, add]
  let copyDest : UInt256 := (⟨128⟩ : UInt256) + ⟨32⟩
  let copyLen : UInt256 := UInt256.ofNat o.size
  have hcopyDest_toNat : copyDest.toNat = 160 := by
    decide
  have hcopyLen_toNat : copyLen.toNat = o.size := by
    simpa [copyLen] using UInt256.toNat_ofNat_of_lt hosz
  let mem4 : ByteArray := o.write 0 mem3 copyDest.toNat copyLen.toNat
  have haw4 :
      UInt256.ofNat (MachineState.M (UInt256.ofNat 5).toNat copyDest.toNat copyLen.toNat) =
        SimpleAuction.withdrawReturnDataActiveWords o := by
    simp [SimpleAuction.withdrawReturnDataActiveWords, copyDest, copyLen, hcopyDest_toNat,
      hcopyLen_toNat]
  have rd1391 := RD.returndatacopy
    (Cₘ (SimpleAuction.withdrawReturnDataActiveWords o) - Cₘ (UInt256.ofNat 5))
    mem4
    (SimpleAuction.withdrawReturnDataActiveWords o)
    rd1390 (by decide)
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, hcopyLen_toNat]; omega)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, copyDest, copyLen,
        SimpleAuction.withdrawReturnDataActiveWords, hcopyDest_toNat, hcopyLen_toNat])
    (by rfl)
    haw4
    (by evm_ov)
  have rd1400 := evm_run rd1391 with [push2 ⟨1400⟩, jump (by jump_dest), jumpdest]
  exact ⟨_, _, _, _, evm_run rd1400 with [pop, pop, swap1, pop]⟩

set_option maxHeartbeats 1000000 in
theorem scratch_blindAuctionRevealX_postCallNonempty_toRequire_freePtr {I} {g : Sat256}
    {s0 : State} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ} {z senderWord refund len freePtr revealEnd biddingEnd valuesLen valuesEnd fakesLen
      fakesEnd secretsLen secretsEnd sel : UInt256}
    {mem : ByteArray} {aw : UInt256} {o : ByteArray}
    (rd : RD blindAuctionBytecode I g s0 ⟨1350⟩
      [z, freePtr, refund, senderWord, ⟨0⟩, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw o acc k C)
    (ho0 : o.size ≠ 0) (hosz : o.size < UInt256.size)
    (hfree :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          (mem.readWithPadding (⟨64⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat))) =
        freePtr) :
    ∃ mem' aw' k' C', RD blindAuctionBytecode I g s0 ⟨1405⟩
      [z, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, sel]
      mem' aw' o acc k' C' := by
  let rdsz : UInt256 := UInt256.ofNat o.size
  have hrdsz_toNat : rdsz.toNat = o.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt hosz
  have hrdsz_ne : rdsz ≠ ⟨0⟩ := by
    intro h
    have hnat : rdsz.toNat = 0 := by rw [h]; rfl
    exact ho0 (by rwa [hrdsz_toNat] at hnat)
  have heq0 : UInt256.eq rdsz (⟨0⟩ : UInt256) = ⟨0⟩ := u256_eq_of_ne hrdsz_ne
  have rd1359₀ := evm_run rd with [swap3, pop, pop, pop, returndatasize, dup1, push0, dup2, eq]
  have rd1359 := rd1359₀
  change UInt256.eq rdsz (⟨0⟩ : UInt256) = ⟨0⟩ at heq0
  rw [show UInt256.ofNat o.size = rdsz from rfl, heq0] at rd1359
  have rd1363 := evm_run rd1359 with [push2 ⟨1395⟩, jumpiNT (by decide)]
  let rounded : UInt256 := UInt256.land (UInt256.add rdsz ⟨63⟩) (UInt256.lnot ⟨31⟩)
  let aw1 : UInt256 :=
    UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let mem2 : ByteArray := (UInt256.toByteArray (UInt256.add freePtr rounded)).write 0 mem 64 32
  let aw2 : UInt256 :=
    UInt256.ofNat (MachineState.M aw1.toNat (⟨64⟩ : UInt256).toNat 32)
  have rd1381 := evm_run rd1363 with [
    push1 ⟨64⟩,
    raw mload (Cₘ aw1 - Cₘ aw) freePtr aw1 (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk, aw1])
      hfree (by rfl) (by evm_ov),
    swap2, pop, push1 ⟨31⟩, not, push1 ⟨63⟩, returndatasize, add, and, dup3, add,
    push1 ⟨64⟩,
    raw mstore (Cₘ aw2 - Cₘ aw1) mem2 aw2 (by decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw2])
      (by rfl) (by rfl) (by evm_ov)]
  let mem3 : ByteArray := (UInt256.toByteArray rdsz).write 0 mem2 freePtr.toNat 32
  let aw3 : UInt256 := UInt256.ofNat (MachineState.M aw2.toNat freePtr.toNat 32)
  have rd1384 := evm_run rd1381 with [
    returndatasize, dup3,
    raw mstore (Cₘ aw3 - Cₘ aw2) mem3 aw3 (by decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw3])
      (by rfl) (by rfl) (by evm_ov)]
  have rd1390 := evm_run rd1384 with [returndatasize, push0, push1 ⟨32⟩, dup5, add]
  let copyDest : UInt256 := freePtr + ⟨32⟩
  let copyLen : UInt256 := UInt256.ofNat o.size
  have hcopyLen_toNat : copyLen.toNat = o.size := by
    simpa [copyLen] using UInt256.toNat_ofNat_of_lt hosz
  let mem4 : ByteArray := o.write 0 mem3 copyDest.toNat copyLen.toNat
  let aw4 : UInt256 := UInt256.ofNat (MachineState.M aw3.toNat copyDest.toNat copyLen.toNat)
  have rd1391 := RD.returndatacopy
    (Cₘ aw4 - Cₘ aw3) mem4 aw4
    rd1390 (by decide)
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, hcopyLen_toNat]; omega)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, copyDest, copyLen, aw4,
        hcopyLen_toNat])
    (by rfl) (by rfl) (by evm_ov)
  have rd1400 := evm_run rd1391 with [push2 ⟨1400⟩, jump (by jump_dest), jumpdest]
  exact ⟨_, _, _, _, evm_run rd1400 with [pop, pop, swap1, pop]⟩

theorem scratch_blindAuctionRevealX_loopExit_toCall {I} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : ℕ}
    {i refund len revealEnd biddingEnd valuesLen valuesEnd fakesLen fakesEnd secretsLen
      secretsEnd sel freePtr : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1331⟩
      [i, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C)
    (hfree :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          (mem.readWithPadding (⟨64⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat))) =
        freePtr)
    (hawM :
      UInt256.ofNat
        (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat) = aw) :
    ∃ gasArg k' C', RD blindAuctionBytecode I g s0 ⟨1349⟩
      [gasArg, revealScratchSenderWord I, refund, freePtr, ⟨0⟩, freePtr, ⟨0⟩,
        freePtr, refund, revealScratchSenderWord I, ⟨0⟩, refund, len,
        revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen,
        valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k' C' := by
  have hawM' :
      UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32) = aw := by
    simpa using hawM
  have rd1348₀ := evm_run rd with [
    jumpdest, pop, push1 ⟨64⟩,
    raw mload 0 freePtr aw
      (by decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        rw [hawM']
        simp)
      hfree
      hawM'
      (by simp),
    push0, swap1, caller, swap1, dup4, swap1, dup4, dup2, dup2, dup2, dup6, dup8]
  obtain ⟨gasArg, rd1349⟩ := rd1348₀.gas (by decide) (by evm_ov)
  exact ⟨gasArg, _, _, by simpa [revealScratchSenderWord] using rd1349⟩

def scratch_revealEvmLoopStack (i refund len revealEnd biddingEnd secretsLen secretsEnd
    fakesLen fakesEnd valuesLen valuesEnd sel : UInt256) : List UInt256 :=
  [i, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd,
    valuesLen, valuesEnd, ⟨276⟩, sel]

noncomputable def scratch_revealBidsArrayDataMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (revealScratchBidsLengthSlot I)).write 0
    (revealScratchBidsHashMem I) 0 32

theorem scratch_revealBidsArrayDataMem_size (I : ExecutionEnv) :
    (scratch_revealBidsArrayDataMem I).size = 96 := by
  unfold scratch_revealBidsArrayDataMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [revealScratchBidsHashMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, revealScratchBidsHashMem_size,
    toByteArray_size]
  omega

theorem scratch_revealBidsArrayDataMem_read0 (I : ExecutionEnv) :
    (scratch_revealBidsArrayDataMem I).readWithPadding 0 32 =
      UInt256.toByteArray (revealScratchBidsLengthSlot I) := by
  unfold scratch_revealBidsArrayDataMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by omega),
    show (UInt256.toByteArray (revealScratchBidsLengthSlot I)).extract 0 32 =
      UInt256.toByteArray (revealScratchBidsLengthSlot I) from by
        apply ByteArray.ext
        rw [ByteArray.data_extract]
        exact Array.extract_eq_self_of_le (by
          change (UInt256.toByteArray (revealScratchBidsLengthSlot I)).size ≤ 32
          rw [toByteArray_size])]

theorem scratch_revealBidsArrayDataMem_read64 (I : ExecutionEnv) :
    (scratch_revealBidsArrayDataMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold scratch_revealBidsArrayDataMem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [revealScratchBidsHashMem_size]; omega) (by omega)
      (by rw [revealScratchBidsHashMem_size]),
    revealScratchBidsHashMem_read64]

theorem scratch_revealBidsArrayDataMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (scratch_revealBidsArrayDataMem I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((scratch_revealBidsArrayDataMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [scratch_revealBidsArrayDataMem_size]; decide) (by decide)
    (scratch_revealBidsArrayDataMem_read64 I)

theorem scratch_revealBidsArrayDataKeccak (I : ExecutionEnv) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((scratch_revealBidsArrayDataMem I).readWithPadding 0 32))) =
      uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (revealScratchBidsLengthSlot I))) := by
  rw [scratch_revealBidsArrayDataMem_read0]
  exact keccakSlot_eq _

theorem scratch_revealBidsElemSlot_eq (I : ExecutionEnv) (i : UInt256) :
    uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (revealScratchBidsLengthSlot I))) +
        UInt256.mul i ⟨2⟩ =
      bidsElemSlot (.address I.source) (.int (Int.ofNat i.toNat)) := by
  unfold revealScratchBidsLengthSlot bidsElemSlot
  rw [keyValueToWord_uint256]
  apply congrArg (fun x => x + UInt256.ofNat (i.toNat * 2)) rfl

theorem scratch_blindAuctionRevealX_loopCond_exit {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1014⟩
      (scratch_revealEvmLoopStack i refund len revealEnd biddingEnd secretsLen secretsEnd
        fakesLen fakesEnd valuesLen valuesEnd sel)
      mem aw rdata acc k C)
    (hbound : len.toNat ≤ i.toNat) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1331⟩
      (scratch_revealEvmLoopStack i refund len revealEnd biddingEnd secretsLen secretsEnd
        fakesLen fakesEnd valuesLen valuesEnd sel)
      mem aw rdata acc k' C' := by
  have hlt : UInt256.lt i len = ⟨0⟩ := ult_zero hbound
  have rd' : RD blindAuctionBytecode I g s0 ⟨1014⟩
      [i, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C := by
    simpa [scratch_revealEvmLoopStack] using rd
  have rd1019₀ := evm_run rd' with [jumpdest, dup3, dup2, lt, iszero]
  have rd1019 := rd1019₀
  rw [hlt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd1019
  exact ⟨_, _, by
    simpa [scratch_revealEvmLoopStack] using
      (evm_run rd1019 with [push2 ⟨1331⟩, jumpiT one_ne_zero_uint (by jump_dest)])⟩


theorem scratch_blindAuctionRevealX_loopBody_toElemSlot {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1023⟩
      (scratch_revealEvmLoopStack i refund len revealEnd biddingEnd secretsLen secretsEnd
        fakesLen fakesEnd valuesLen valuesEnd sel)
      mem aw rdata acc k C)
    (haw0 : UInt256.ofNat (MachineState.M aw.toNat 0 32) = aw)
    (haw32 : UInt256.ofNat (MachineState.M aw.toNat 32 32) = aw)
    (haw64 : UInt256.ofNat (MachineState.M aw.toNat 0 64) = aw)
    (hbaseHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC
          (((UInt256.toByteArray (⟨4⟩ : UInt256)).write 0
            ((UInt256.toByteArray (revealScratchSenderWord I)).write 0 mem 0 32)
              32 32).readWithPadding 0 64))) =
        revealScratchBidsLengthSlot I)
    (hlenLoad :
      (acc.2.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (revealScratchBidsLengthSlot I) ⟨0⟩) = len)
    (hbound : i.toNat < len.toNat)
    (hdataHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC
          (((UInt256.toByteArray (revealScratchBidsLengthSlot I)).write 0
            ((UInt256.toByteArray (⟨4⟩ : UInt256)).write 0
              ((UInt256.toByteArray (revealScratchSenderWord I)).write 0 mem 0 32)
              32 32) 0 32).readWithPadding 0 32))) =
        uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (revealScratchBidsLengthSlot I)))) :
    ∃ mem' aw' k' C', RD blindAuctionBytecode I g s0 ⟨1069⟩
      [bidsElemSlot (.address I.source) (.int (Int.ofNat i.toNat)), i, refund, len, revealEnd,
        biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem' aw' rdata acc k' C' := by
  let mem1 : ByteArray := (UInt256.toByteArray (revealScratchSenderWord I)).write 0 mem 0 32
  let mem2 : ByteArray := (UInt256.toByteArray (⟨4⟩ : UInt256)).write 0 mem1 32 32
  let mem3 : ByteArray := (UInt256.toByteArray (revealScratchBidsLengthSlot I)).write 0 mem2 0 32
  have rd' : RD blindAuctionBytecode I g s0 ⟨1023⟩
      [i, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C := by
    simpa [scratch_revealEvmLoopStack] using rd
  have rd1027 := evm_run rd' with [
    caller, push0, swap1, dup2,
    raw mstore 0 mem1 aw (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [haw0]
        simp)
      (by rfl) haw0 (by evm_ov)]
  have rd1033 := evm_run rd1027 with [
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0 mem2 aw (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [show (⟨32⟩ : UInt256).toNat = 32 by native_decide]
        rw [haw32]
        simp)
      (by rfl) haw32 (by evm_ov),
    push1 ⟨64⟩, dup2,
    raw keccak256 0 (revealScratchBidsLengthSlot I) aw (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [show (⟨64⟩ : UInt256).toNat = 64 by native_decide]
        rw [haw64]
        simp)
      (by simpa [mem2, mem1, revealScratchSenderWord] using hbaseHash) haw64
      (by evm_ov),
    dup1]
  obtain ⟨_, _, rd1039₀⟩ := rd1033.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1039⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1039⟩
      [len, revealScratchBidsLengthSlot I, ⟨0⟩, i, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem2 aw rdata acc k' C' := by
    exact ⟨_, _, by simpa [hlenLoad] using rd1039₀⟩
  have hlt : UInt256.lt i len = ⟨1⟩ := ult_one hbound
  have rd1047₀ := evm_run rd1039 with [dup4, swap1, dup2, lt]
  have rd1047 := rd1047₀
  rw [hlt] at rd1047
  have rd1054 := evm_run rd1047 with [
    push2 ⟨1054⟩, jumpiT one_ne_zero_uint (by jump_dest), jumpdest]
  have rd1062 := evm_run rd1054 with [
    swap1, push0,
    raw mstore 0 mem3 aw (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [haw0]
        simp)
      (by rfl) haw0 (by evm_ov),
    push1 ⟨32⟩, push0,
    raw keccak256 0
      (uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (revealScratchBidsLengthSlot I))))
      aw (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [show (⟨32⟩ : UInt256).toNat = 32 by native_decide]
        rw [haw0]
        simp)
      (by simpa [mem3, mem2, mem1, revealScratchSenderWord] using hdataHash) haw0
      (by evm_ov)]
  have hslot :
      UInt256.mul ⟨2⟩ i +
          uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (revealScratchBidsLengthSlot I))) =
        bidsElemSlot (.address I.source) (.int (Int.ofNat i.toNat)) := by
    have hmul : UInt256.mul ⟨2⟩ i = UInt256.mul i ⟨2⟩ := by
      apply u256_inj
      show ((⟨2⟩ : UInt256).val * i.val).val = (i.val * (⟨2⟩ : UInt256).val).val
      rw [Fin.val_mul, Fin.val_mul, Nat.mul_comm]
    rw [hmul]
    rw [u256_add_comm]
    exact scratch_revealBidsElemSlot_eq I i
  have rd1069 := evm_run rd1062 with [swap1, push1 ⟨2⟩, mul, add, swap1, pop]
  have hpc1069 :
      (⟨1054⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ :
          UInt256) = ⟨1069⟩ := by
    native_decide
  exact ⟨mem3, aw, _, _, by simpa [hslot, hpc1069] using rd1069⟩

theorem scratch_RD_decodeRawBool_zero {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {start endOffset ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    (rd : RD blindAuctionBytecode I g s0 ⟨1987⟩ (start :: endOffset :: ret :: R)
      mem aw rdata acc k C)
    (hslt : UInt256.slt (UInt256.sub endOffset start) ⟨32⟩ = ⟨0⟩)
    (hword : uInt256OfByteArray (I.calldata.readBytes start.toNat 32) = ⟨0⟩)
    (hret : (D_J blindAuctionBytecode 0).contains ret = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ret (⟨0⟩ :: R)
      mem aw rdata acc k' C' := by
  have rd2003 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero,
    push2 ⟨2003⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, dup2, calldataload, dup1, iszero, iszero, dup2, eq]
  have rd2003' := rd2003
  rw [hword] at rd2003'
  have rd2018 := evm_run rd2003' with [
    push2 ⟨2018⟩, jumpiT (by decide) (by jump_dest), jumpdest]
  exact ⟨_, _, evm_run rd2018 with [swap4, swap3, pop, pop, pop, jump hret]⟩

theorem scratch_RD_decodeRawBool_one {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {start endOffset ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    (rd : RD blindAuctionBytecode I g s0 ⟨1987⟩ (start :: endOffset :: ret :: R)
      mem aw rdata acc k C)
    (hslt : UInt256.slt (UInt256.sub endOffset start) ⟨32⟩ = ⟨0⟩)
    (hword : uInt256OfByteArray (I.calldata.readBytes start.toNat 32) = ⟨1⟩)
    (hret : (D_J blindAuctionBytecode 0).contains ret = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ret (⟨1⟩ :: R)
      mem aw rdata acc k' C' := by
  have rd2003 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero,
    push2 ⟨2003⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, dup2, calldataload, dup1, iszero, iszero, dup2, eq]
  have rd2003' := rd2003
  rw [hword] at rd2003'
  have rd2018 := evm_run rd2003' with [
    push2 ⟨2018⟩, jumpiT (by decide) (by jump_dest), jumpdest]
  exact ⟨_, _, evm_run rd2018 with [swap4, swap3, pop, pop, pop, jump hret]⟩

theorem scratch_RD_decodeRawBool_invalid_revert {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {start endOffset ret word : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    (rd : RD blindAuctionBytecode I g s0 ⟨1987⟩ (start :: endOffset :: ret :: R)
      mem aw rdata acc k C)
    (hslt : UInt256.slt (UInt256.sub endOffset start) ⟨32⟩ = ⟨0⟩)
    (hword : uInt256OfByteArray (I.calldata.readBytes start.toNat 32) = word)
    (hzero : word ≠ ⟨0⟩)
    (hone : word ≠ ⟨1⟩)
    (hov : R.length + 10 ≤ 1024) :
    RDrev blindAuctionBytecode g s0 := by
  have hboolWord :
      UInt256.eq word (UInt256.isZero (UInt256.isZero word)) = ⟨0⟩ := by
    have hz : UInt256.isZero word = ⟨0⟩ := isZero_eq_zero_of_ne hzero
    have ho : UInt256.isZero (UInt256.isZero word) = ⟨1⟩ := by
      rw [hz]
      rfl
    rw [ho]
    exact u256_eq_of_ne hone
  have rd2003 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero,
    push2 ⟨2003⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, dup2, calldataload, dup1, iszero, iszero, dup2, eq]
  have rd2003' := rd2003
  rw [hword, hboolWord] at rd2003'
  have rd2015 := evm_run rd2003' with [push2 ⟨2018⟩, jumpiNT (by decide)]
  exact rd2015.revertStub (by decide) (by decide) (by decide) (by simp; omega)

set_option maxHeartbeats 2000000 in
theorem scratch_blindAuctionRevealX_loopBody_loads_toFakeDecoder {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel value : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1069⟩
      [slot, i, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen,
        fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C)
    (hvalueBound : i.toNat < valuesLen.toNat)
    (hfakesBound : i.toNat < fakesLen.toNat)
    (hvalueLoad :
      uInt256OfByteArray
          (I.calldata.readBytes (UInt256.mul ⟨32⟩ i + valuesEnd).toNat 32) =
        value) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1987⟩
      [UInt256.mul ⟨32⟩ i + fakesEnd, UInt256.mul ⟨32⟩ i + fakesEnd + ⟨32⟩, ⟨1135⟩,
        value, ⟨0⟩, ⟨0⟩, ⟨0⟩, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k' C' := by
  have hvalueLt : UInt256.lt i valuesLen = ⟨1⟩ := ult_one hvalueBound
  have rd1078₀ := evm_run rd with [
    push0, push0, push0, dup15, dup15, dup7, dup2, dup2, lt]
  have rd1078 := rd1078₀
  rw [hvalueLt] at rd1078
  have rd1096₀ := evm_run rd1078 with [
    push2 ⟨1089⟩, jumpiT one_ne_zero_uint (by jump_dest), jumpdest, swap1, pop,
    push1 ⟨32⟩, mul, add, calldataload]
  have rd1096 := rd1096₀
  rw [hvalueLoad] at rd1096
  have hfakesLt : UInt256.lt i fakesLen = ⟨1⟩ := ult_one hfakesBound
  have rd1102₀ := evm_run rd1096 with [dup14, dup14, dup8, dup2, dup2, lt]
  have rd1102 := rd1102₀
  rw [hfakesLt] at rd1102
  have rd1134 := evm_run rd1102 with [
    push2 ⟨1114⟩, jumpiT one_ne_zero_uint (by jump_dest), jumpdest, swap1, pop,
    push1 ⟨32⟩, mul, add, push1 ⟨32⟩, dup2, add, swap1, push2 ⟨1135⟩, swap2,
    swap1, push2 ⟨1987⟩, jump (by jump_dest)]
  exact ⟨_, _, by simpa using rd1134⟩

set_option maxHeartbeats 3000000 in
theorem scratch_blindAuctionRevealX_loopBody_fakeDecoder_zero_toBool {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel value : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1987⟩
      [UInt256.mul ⟨32⟩ i + fakesEnd, UInt256.mul ⟨32⟩ i + fakesEnd + ⟨32⟩, ⟨1135⟩,
        value, ⟨0⟩, ⟨0⟩, ⟨0⟩, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C)
    (hfakeSlt :
      UInt256.slt
          (UInt256.sub
            (UInt256.mul ⟨32⟩ i + fakesEnd + ⟨32⟩)
            (UInt256.mul ⟨32⟩ i + fakesEnd)) ⟨32⟩ = ⟨0⟩)
    (hfakeLoad :
      uInt256OfByteArray
          (I.calldata.readBytes (UInt256.mul ⟨32⟩ i + fakesEnd).toNat 32) = ⟨0⟩) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1135⟩
      [⟨0⟩, value, ⟨0⟩, ⟨0⟩, ⟨0⟩, slot, i, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k' C' := by
  have rd2003 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero,
    push2 ⟨2003⟩, jumpiT (by rw [hfakeSlt]; decide) (by jump_dest),
    jumpdest, dup2, calldataload, dup1, iszero, iszero, dup2, eq]
  have rd2003' := rd2003
  rw [hfakeLoad] at rd2003'
  have rd2018 := evm_run rd2003' with [
    push2 ⟨2018⟩, jumpiT (by decide) (by jump_dest), jumpdest]
  exact ⟨_, _, evm_run rd2018 with [swap4, swap3, pop, pop, pop, jump (by jump_dest)]⟩

set_option maxHeartbeats 3000000 in
theorem scratch_blindAuctionRevealX_loopBody_fakeDecoder_one_toBool {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel value : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1987⟩
      [UInt256.mul ⟨32⟩ i + fakesEnd, UInt256.mul ⟨32⟩ i + fakesEnd + ⟨32⟩, ⟨1135⟩,
        value, ⟨0⟩, ⟨0⟩, ⟨0⟩, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C)
    (hfakeSlt :
      UInt256.slt
          (UInt256.sub
            (UInt256.mul ⟨32⟩ i + fakesEnd + ⟨32⟩)
            (UInt256.mul ⟨32⟩ i + fakesEnd)) ⟨32⟩ = ⟨0⟩)
    (hfakeLoad :
      uInt256OfByteArray
          (I.calldata.readBytes (UInt256.mul ⟨32⟩ i + fakesEnd).toNat 32) = ⟨1⟩) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1135⟩
      [⟨1⟩, value, ⟨0⟩, ⟨0⟩, ⟨0⟩, slot, i, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k' C' := by
  have rd2003 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero,
    push2 ⟨2003⟩, jumpiT (by rw [hfakeSlt]; decide) (by jump_dest),
    jumpdest, dup2, calldataload, dup1, iszero, iszero, dup2, eq]
  have rd2003' := rd2003
  rw [hfakeLoad] at rd2003'
  have rd2018 := evm_run rd2003' with [
    push2 ⟨2018⟩, jumpiT (by decide) (by jump_dest), jumpdest]
  exact ⟨_, _, evm_run rd2018 with [swap4, swap3, pop, pop, pop, jump (by jump_dest)]⟩

set_option maxHeartbeats 3000000 in
theorem scratch_blindAuctionRevealX_loopBody_fakeDecoder_invalid_revert {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel value word : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1987⟩
      [UInt256.mul ⟨32⟩ i + fakesEnd, UInt256.mul ⟨32⟩ i + fakesEnd + ⟨32⟩, ⟨1135⟩,
        value, ⟨0⟩, ⟨0⟩, ⟨0⟩, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C)
    (hfakeSlt :
      UInt256.slt
          (UInt256.sub
            (UInt256.mul ⟨32⟩ i + fakesEnd + ⟨32⟩)
            (UInt256.mul ⟨32⟩ i + fakesEnd)) ⟨32⟩ = ⟨0⟩)
    (hfakeLoad :
      uInt256OfByteArray
          (I.calldata.readBytes (UInt256.mul ⟨32⟩ i + fakesEnd).toNat 32) = word)
    (hzero : word ≠ ⟨0⟩)
    (hone : word ≠ ⟨1⟩) :
    RDrev blindAuctionBytecode g s0 := by
  have hboolWord :
      UInt256.eq word (UInt256.isZero (UInt256.isZero word)) = ⟨0⟩ := by
    have hz : UInt256.isZero word = ⟨0⟩ := isZero_eq_zero_of_ne hzero
    have ho : UInt256.isZero (UInt256.isZero word) = ⟨1⟩ := by
      rw [hz]
      rfl
    rw [ho]
    exact u256_eq_of_ne hone
  have rd2003 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero,
    push2 ⟨2003⟩, jumpiT (by rw [hfakeSlt]; decide) (by jump_dest),
    jumpdest, dup2, calldataload, dup1, iszero, iszero, dup2, eq]
  have rd2003' := rd2003
  rw [hfakeLoad, hboolWord] at rd2003'
  have rd2015 := evm_run rd2003' with [push2 ⟨2018⟩, jumpiNT (by decide)]
  exact rd2015.revertStub (by decide) (by decide) (by decide) (by simp)

set_option maxHeartbeats 2000000 in
theorem scratch_blindAuctionRevealX_loopBody_secret_toPacked {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {fakeWord value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd
      valuesLen valuesEnd sel secret : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1135⟩
      [fakeWord, value, ⟨0⟩, ⟨0⟩, ⟨0⟩, slot, i, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C)
    (hsecretsBound : i.toNat < secretsLen.toNat)
    (hsecretLoad :
      uInt256OfByteArray
          (I.calldata.readBytes (UInt256.mul ⟨32⟩ i + secretsEnd).toNat 32) =
        secret) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1167⟩
      [secret, fakeWord, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k' C' := by
  have hsecretsLt : UInt256.lt i secretsLen = ⟨1⟩ := ult_one hsecretsBound
  have rd1141₀ := evm_run rd with [jumpdest, dup13, dup13, dup9, dup2, dup2, lt]
  have rd1141 := rd1141₀
  rw [hsecretsLt] at rd1141
  have rd1160₀ := evm_run rd1141 with [
    push2 ⟨1153⟩, jumpiT one_ne_zero_uint (by jump_dest), jumpdest, swap1, pop,
    push1 ⟨32⟩, mul, add, calldataload]
  have rd1160 := rd1160₀
  rw [hsecretLoad] at rd1160
  have rd1167 := evm_run rd1160 with [swap3, pop, swap3, pop, swap3, pop]
  exact ⟨_, _, by simpa using rd1167⟩

noncomputable def scratch_revealPackedValueMem (mem : ByteArray) (base value : UInt256) :
    ByteArray :=
  (UInt256.toByteArray value).write 0 mem base.toNat 32

noncomputable def scratch_revealPackedFakeMem (mem : ByteArray) (base fakeWord : UInt256) :
    ByteArray :=
  (UInt256.toByteArray (UInt256.shiftLeft (UInt256.isZero (UInt256.isZero fakeWord)) ⟨248⟩)).write
    0 mem base.toNat 32

noncomputable def scratch_revealPackedSecretMem (mem : ByteArray) (base secret : UInt256) :
    ByteArray :=
  (UInt256.toByteArray secret).write 0 mem base.toNat 32

noncomputable def scratch_revealPackedLenMem (mem : ByteArray) (base len : UInt256) :
    ByteArray :=
  (UInt256.toByteArray len).write 0 mem base.toNat 32

noncomputable def scratch_revealPackedFreePtrMem (mem : ByteArray) (freePtr : UInt256) :
    ByteArray :=
  (UInt256.toByteArray freePtr).write 0 mem 64 32

set_option maxHeartbeats 1200000 in
theorem scratch_blindAuctionRevealX_loopBody_packed_prefix {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {secret fakeWord value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel fp : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1167⟩
      [secret, fakeWord, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C)
    (hfp :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = fp) :
    ∃ k' C',
      let aw1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
      let base := (⟨32⟩ : UInt256) + fp
      let fakeBase := base + ⟨32⟩
      let secretBase := base + ⟨33⟩
      let newFree := (⟨65⟩ : UInt256) + base
      let mem1 := scratch_revealPackedValueMem mem base value
      let aw2 := UInt256.ofNat (MachineState.M aw1.toNat base.toNat 32)
      let mem2 := scratch_revealPackedFakeMem mem1 fakeBase fakeWord
      let aw3 := UInt256.ofNat (MachineState.M aw2.toNat fakeBase.toNat 32)
      let mem3 := scratch_revealPackedSecretMem mem2 secretBase secret
      let aw4 := UInt256.ofNat (MachineState.M aw3.toNat secretBase.toNat 32)
      RD blindAuctionBytecode I g s0 ⟨1207⟩
        [newFree, secret, fakeWord, value, slot, i, refund, len, revealEnd, biddingEnd,
          secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
        mem3 aw4 rdata acc k' C' := by
  let aw1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let base := (⟨32⟩ : UInt256) + fp
  let fakeBase := base + ⟨32⟩
  let secretBase := base + ⟨33⟩
  let newFree := (⟨65⟩ : UInt256) + base
  let mem1 := scratch_revealPackedValueMem mem base value
  let aw2 := UInt256.ofNat (MachineState.M aw1.toNat base.toNat 32)
  let mem2 := scratch_revealPackedFakeMem mem1 fakeBase fakeWord
  let aw3 := UInt256.ofNat (MachineState.M aw2.toNat fakeBase.toNat 32)
  let mem3 := scratch_revealPackedSecretMem mem2 secretBase secret
  let aw4 := UInt256.ofNat (MachineState.M aw3.toNat secretBase.toNat 32)
  have rd1185 := evm_run rd with [
    dup3, dup3, dup3, push1 ⟨64⟩,
    raw mload (Cₘ aw1 - Cₘ aw) fp aw1 (by decide)
      (fun s haws hstks => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, aw1])
      hfp (by rfl) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨1207⟩, swap4, swap3, swap2, swap1, swap3, dup4,
    raw mstore (Cₘ aw2 - Cₘ aw1) mem1 aw2 (by decide)
      (fun s haws hstks => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, base, aw2])
      (by rfl) (by rfl) (by evm_ov)]
  have rd1207 := evm_run rd1185 with [
    swap1, iszero, iszero, push1 ⟨248⟩, shl, push1 ⟨32⟩, dup4, add,
    raw mstore (Cₘ aw3 - Cₘ aw2) mem2 aw3 (by decide)
      (fun s haws hstks => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, base, fakeBase,
          aw3])
      (by rfl) (by rfl) (by evm_ov),
    push1 ⟨33⟩, dup3, add,
    raw mstore (Cₘ aw4 - Cₘ aw3) mem3 aw4 (by decide)
      (fun s haws hstks => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, base, secretBase,
          aw4])
      (by rfl) (by rfl) (by evm_ov),
    push1 ⟨65⟩, add, swap1, jump (by jump_dest)]
  exact ⟨_, _, by
    simpa [aw1, base, fakeBase, secretBase, newFree, mem1, mem2, mem3, aw2, aw3, aw4]
      using rd1207⟩

set_option maxHeartbeats 1200000 in
theorem scratch_blindAuctionRevealX_loopBody_packed_suffix {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {secret fakeWord value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel fp hash blinded flag : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1207⟩
      [((⟨65⟩ : UInt256) + ((⟨32⟩ : UInt256) + fp)), secret, fakeWord, value, slot,
        i, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen,
        fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hfp :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = fp)
    (hlen :
      let base := (⟨32⟩ : UInt256) + fp
      let newFree := (⟨65⟩ : UInt256) + base
      let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
      let mem4 := scratch_revealPackedLenMem mem fp packedLen
      let aw1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
      let aw2 := UInt256.ofNat (MachineState.M aw1.toNat fp.toNat 32)
      let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
      let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨64⟩ : UInt256).toNat 32)
      (if fp.toNat ≥ mem5.size ∨ fp ≥ aw3 * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem5.readWithPadding fp.toNat 32))) =
        packedLen)
    (hhash :
      let base := (⟨32⟩ : UInt256) + fp
      let newFree := (⟨65⟩ : UInt256) + base
      let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
      let mem4 := scratch_revealPackedLenMem mem fp packedLen
      let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
      UInt256.ofNat
          (fromByteArrayBigEndian (ffi.KEC (mem5.readWithPadding base.toNat packedLen.toNat))) =
        hash)
    (hstore :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD ((⟨0⟩ : UInt256) + slot) ⟨0⟩) = blinded)
    (hflag : UInt256.eq blinded hash = flag) :
    ∃ k' C',
      let base := (⟨32⟩ : UInt256) + fp
      let newFree := (⟨65⟩ : UInt256) + base
      let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
      let mem4 := scratch_revealPackedLenMem mem fp packedLen
      let aw1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
      let aw2 := UInt256.ofNat (MachineState.M aw1.toNat fp.toNat 32)
      let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
      let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨64⟩ : UInt256).toNat 32)
      let aw4 := UInt256.ofNat (MachineState.M aw3.toNat fp.toNat 32)
      let aw5 := UInt256.ofNat (MachineState.M aw4.toNat base.toNat packedLen.toNat)
      RD blindAuctionBytecode I g s0 ⟨1235⟩
        [flag, secret, fakeWord, value, slot, i, refund, len, revealEnd, biddingEnd,
          secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
        mem5 aw5 rdata (cA, σ) k' C' := by
  let base := (⟨32⟩ : UInt256) + fp
  let newFree := (⟨65⟩ : UInt256) + base
  let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
  let mem4 := scratch_revealPackedLenMem mem fp packedLen
  let aw1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let aw2 := UInt256.ofNat (MachineState.M aw1.toNat fp.toNat 32)
  let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
  let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨64⟩ : UInt256).toNat 32)
  let aw4 := UInt256.ofNat (MachineState.M aw3.toNat fp.toNat 32)
  let aw5 := UInt256.ofNat (MachineState.M aw4.toNat base.toNat packedLen.toNat)
  have rd1224 := evm_run rd with [
    jumpdest, push1 ⟨64⟩,
    raw mload (Cₘ aw1 - Cₘ aw) fp aw1 (by decide)
      (fun s haws hstks => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, aw1])
      hfp (by rfl) (by evm_ov),
    push1 ⟨32⟩, dup2, dup4, sub, sub, dup2,
    raw mstore (Cₘ aw2 - Cₘ aw1) mem4 aw2 (by decide)
      (fun s haws hstks => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, aw2])
      (by rfl) (by rfl) (by evm_ov),
    swap1, push1 ⟨64⟩,
    raw mstore (Cₘ aw3 - Cₘ aw2) mem5 aw3 (by decide)
      (fun s haws hstks => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, aw3])
      (by rfl) (by rfl) (by evm_ov),
    dup1,
    raw mload (Cₘ aw4 - Cₘ aw3) packedLen aw4 (by decide)
      (fun s haws hstks => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, aw4])
      (by simpa [base, newFree, packedLen, mem4, mem5, aw1, aw2, aw3] using hlen)
      (by rfl) (by evm_ov)]
  have rd1233₀ := evm_run rd1224 with [
    swap1, push1 ⟨32⟩, add,
    raw keccak256 (Cₘ aw5 - Cₘ aw4) hash aw5 (by decide)
      (fun s haws hstks => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, base, aw5])
      (by simpa [base, newFree, packedLen, mem4, mem5] using hhash)
      (by rfl) (by evm_ov),
    dup5, push0, add]
  obtain ⟨_, _, rd1234₀⟩ := rd1233₀.sload (by decide) (by evm_ov)
  have rd1234 := rd1234₀
  rw [hstore] at rd1234
  have rd1235₀ := evm_run rd1234 with [eq]
  have rd1235 := rd1235₀
  rw [hflag] at rd1235
  exact ⟨_, _, by
    simpa [base, newFree, packedLen, mem4, mem5, aw1, aw2, aw3, aw4, aw5] using rd1235⟩

theorem scratch_blindAuctionRevealX_zeroBlinded_toNext {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {secret fake value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1315⟩
      [secret, fake, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hperm : I.perm = true) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1014⟩
      (scratch_revealEvmLoopStack (i + ⟨1⟩) refund len revealEnd biddingEnd secretsLen
        secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
      mem aw rdata (cA, sstoreAccountMap I.codeOwner σ slot ⟨0⟩) k' C' := by
  have rd1321₀ := evm_run rd with [jumpdest, pop, pop, push0, swap1, swap2]
  obtain ⟨_, _, rd1322₀⟩ := rd1321₀.sstore hperm (by decide) (by evm_ov)
  have rd1323 := evm_run rd1322₀ with [pop, jumpdest, push1 ⟨1⟩, add,
    push2 ⟨1014⟩, jump (by jump_dest)]
  have hidx : (⟨1⟩ : UInt256) + i = i + ⟨1⟩ := u256_add_comm _ _
  exact ⟨_, _, by simpa [scratch_revealEvmLoopStack, sstoreAccountMap, hidx] using rd1323⟩

theorem scratch_blindAuctionRevealX_hashMismatch_toNext {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {secret fake value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1239⟩
      [secret, fake, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1014⟩
      (scratch_revealEvmLoopStack (i + ⟨1⟩) refund len revealEnd biddingEnd secretsLen
        secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
      mem aw rdata acc k' C' := by
  have rd1323 := evm_run rd with [pop, pop, pop, pop, push2 ⟨1323⟩,
    jump (by jump_dest), jumpdest, push1 ⟨1⟩, add, push2 ⟨1014⟩,
    jump (by jump_dest)]
  have hidx : (⟨1⟩ : UInt256) + i = i + ⟨1⟩ := u256_add_comm _ _
  exact ⟨_, _, by simpa [scratch_revealEvmLoopStack, hidx] using rd1323⟩

theorem scratch_blindAuctionRevealX_hashGuard_mismatch_toNext {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {secret fake value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1235⟩
      [⟨0⟩, secret, fake, value, slot, i, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1014⟩
      (scratch_revealEvmLoopStack (i + ⟨1⟩) refund len revealEnd biddingEnd secretsLen
        secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
      mem aw rdata acc k' C' := by
  have rd1239 := evm_run rd with [push2 ⟨1247⟩, jumpiNT (by decide)]
  exact scratch_blindAuctionRevealX_hashMismatch_toNext rd1239

theorem scratch_blindAuctionRevealX_hashGuard_match_to1247 {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {secret fake value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1235⟩
      [⟨1⟩, secret, fake, value, slot, i, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1247⟩
      [secret, fake, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k' C' := by
  exact ⟨_, _, evm_run rd with [push2 ⟨1247⟩, jumpiT one_ne_zero_uint (by jump_dest)]⟩

theorem scratch_blindAuctionRevealX_callMade_fromCall {cA gh bl σ σ₀ A I} {g : Sat256}
    {k C : ℕ}
    {gasArg refund len freePtr revealEnd biddingEnd valuesLen valuesEnd fakesLen fakesEnd
      secretsLen secretsEnd sel : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hbalance : refund ≤ (σ.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : I.depth.val < 1024)
    (rd : RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1349⟩
      [gasArg, revealScratchSenderWord I, refund, freePtr, ⟨0⟩, freePtr, ⟨0⟩,
        freePtr, refund, revealScratchSenderWord I, ⟨0⟩, refund, len,
        revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen,
        valuesEnd, ⟨276⟩, sel]
      mem aw ByteArray.empty (cA, σ) k C)
    (hawCall :
      UInt256.ofNat
        (MachineState.M (MachineState.M aw.toNat freePtr.toNat (⟨0⟩ : UInt256).toNat)
          freePtr.toNat (⟨0⟩ : UInt256).toNat) = aw) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA
          (initState cA gh bl σ σ₀ g A I).genesisBlockHeader
          (initState cA gh bl σ σ₀ g A I).blocks
          σ (initState cA gh bl σ σ₀ g A I).σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (revealScratchSenderWord I))
          (toExecute σ (AccountAddress.ofUInt256 (revealScratchSenderWord I)))
          callGas (UInt256.ofNat I.gasPrice) refund refund
          ByteArray.empty (I.depth + 1) I.header I.perm)
      ∧ o.size < UInt256.size
      ∧ RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1350⟩
          [(if z then ⟨1⟩ else ⟨0⟩), freePtr, refund, revealScratchSenderWord I,
            ⟨0⟩, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen,
            fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
          mem aw o (cA', σ') k' C' := by
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ, rd1350₀, hoSize⟩ :=
    RD.callValueMadeEmptyInOut rd (by decide) hperm hbalance hdepth (by simp)
  have hawCall' :
      UInt256.ofNat
        (MachineState.M (MachineState.M aw.toNat freePtr.toNat 0) freePtr.toNat 0) = aw := by
    simpa using hawCall
  have hpc : (⟨1349⟩ : UInt256) + ⟨1⟩ = ⟨1350⟩ := by
    decide
  exact ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ, hoSize,
    by simpa [revealScratchSenderWord, hpc, hawCall'] using rd1350₀⟩

def scratch_revealPackedBytes (value : UInt256) (fake : Bool) (secret : UInt256) : List UInt8 :=
  EVM.Word.toBytesBE value ++ [if fake then (1 : UInt8) else 0] ++ EVM.Word.toBytesBE secret

def scratch_revealPackedHashExpr : Expr :=
  .keccak256 (.abiEncodePacked
    [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])

def scratch_revealPackedHashValue (value : UInt256) (fake : Bool) (secret : UInt256) : Value :=
  .fixedBytes ⟨31, bytes32._proof_1⟩
    (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray)).toList

theorem scratch_encodePacked_uint256 (value : UInt256) :
    encodePackedValue? uint256 (.int (Int.ofNat value.toNat)) =
      some (EVM.Word.toBytesBE value) := by
  have hword : EVM.word value.toNat = value := u256_ofNat_toNat value
  have hlt : value.toNat < EVM.twoPow 256 := by
    change value.val.val < EVM.twoPow 256
    exact value.val.isLt
  simp [encodePackedValue?, uint256, uint256Int, encodeABIWord?, hword, hlt]

theorem scratch_encodePacked_bool (fake : Bool) :
    encodePackedValue? boolTy (.bool fake) = some [if fake then (1 : UInt8) else 0] := by
  cases fake <;> simp [encodePackedValue?, boolTy]

theorem scratch_encodePacked_bytes32 (secret : UInt256) :
    encodePackedValue? bytes32
      (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)) =
        some (EVM.Word.toBytesBE secret) := by
  have hlen := scratch_word_toBytesBE_length_32 secret
  simp [encodePackedValue?, bytes32, fixedBytesSize, hlen]

/-! ### Ported dynamic decode failure bridge -/

theorem scratch_word_le_solcMax_of_ugt_zero {w : UInt256}
    (h : UInt256.gt w revealMaxU64 = ⟨0⟩) :
    w.toNat ≤ solcMaxU64 := by
  by_contra hle
  have hgt : UInt256.gt w revealMaxU64 = ⟨1⟩ := by
    apply ugt_one
    rw [show revealMaxU64.toNat = solcMaxU64 by native_decide]
    omega
  rw [h] at hgt
  have hnat := congrArg UInt256.toNat hgt
  change (0 : Nat) = 1 at hnat
  omega

theorem scratch_not_solcMax_lt_of_ugt_zero {w : UInt256}
    (h : UInt256.gt w revealMaxU64 = ⟨0⟩) :
    ¬ solcMaxU64 < w.toNat := by
  have hle := scratch_word_le_solcMax_of_ugt_zero h
  omega

theorem scratch_add4_word_add31_toNat (w : UInt256)
    (hle : w.toNat ≤ solcMaxU64) :
    (((⟨4⟩ : UInt256) + w) + ⟨31⟩).toNat = 4 + w.toNat + 31 := by
  rw [← u256_ofNat_toNat w]
  simpa [u256_ofNat_toNat] using
    (uadd3_ofNat_toNat (a := 4) (b := w.toNat) (c := 31)
    (by norm_num [UInt256.size])
    w.val.isLt
    (by norm_num [UInt256.size])
    (by
      rw [show solcMaxU64 = 18446744073709551615 by rfl] at hle
      norm_num [UInt256.size]
      omega)
    (by
      rw [show solcMaxU64 = 18446744073709551615 by rfl] at hle
      norm_num [UInt256.size]
      omega))

theorem scratch_add4_word_toNat (w : UInt256)
    (hle : w.toNat ≤ solcMaxU64) :
    ((⟨4⟩ : UInt256) + w).toNat = 4 + w.toNat := by
  rw [← u256_ofNat_toNat w]
  simpa [u256_ofNat_toNat] using
    (uadd_ofNat_toNat (a := 4) (b := w.toNat)
      (by norm_num [UInt256.size])
      w.val.isLt
      (by
        rw [show solcMaxU64 = 18446744073709551615 by rfl] at hle
        norm_num [UInt256.size]
        omega))

theorem scratch_start_bound_of_slt_one {I : ExecutionEnv} {off : UInt256}
    (hcalldataSign : I.calldata.size < 2 ^ 255)
    (hoff : off.toNat ≤ solcMaxU64)
    (hstart : UInt256.slt (((⟨4⟩ : UInt256) + off) + ⟨31⟩)
      (UInt256.ofNat I.calldata.size) = ⟨1⟩) :
    4 + off.toNat + 31 < I.calldata.size := by
  by_contra hnot
  have hleft :
      (((⟨4⟩ : UInt256) + off) + ⟨31⟩).toNat = 4 + off.toNat + 31 :=
    scratch_add4_word_add31_toNat off hoff
  have hhi : (((⟨4⟩ : UInt256) + off) + ⟨31⟩).toNat < 2 ^ 255 := by
    rw [hleft]
    rw [show solcMaxU64 = 18446744073709551615 by rfl] at hoff
    omega
  have hzero :
      UInt256.slt (((⟨4⟩ : UInt256) + off) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
    apply slt_lit_zero hcalldataSign
    · rw [hleft]
      omega
    · exact hhi
  rw [hstart] at hzero
  have hnat := congrArg UInt256.toNat hzero
  change (1 : Nat) = 0 at hnat
  omega

theorem scratch_array_end_bound_of_ugt_zero {I : ExecutionEnv} {off len : UInt256}
    (hoff : off.toNat ≤ solcMaxU64)
    (hlen : len.toNat ≤ solcMaxU64)
    (hend : UInt256.gt (((((⟨4⟩ : UInt256) + off) +
          UInt256.shiftLeft len ⟨5⟩) + ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) :
    4 + off.toNat + 32 + 32 * len.toNat ≤ I.calldata.size := by
  have h32lenSmall : 32 * len.toNat < UInt256.size := by
    rw [show solcMaxU64 = 18446744073709551615 by rfl] at hlen
    norm_num [UInt256.size]
    omega
  have hleft :
      (((((⟨4⟩ : UInt256) + off) + UInt256.shiftLeft len ⟨5⟩) + ⟨32⟩)).toNat =
        4 + off.toNat + 32 * len.toNat + 32 := by
    rw [← u256_ofNat_toNat off, ← u256_ofNat_toNat len,
      shiftLeft5_ofNat_eq h32lenSmall]
    have h4off32len :
        ((UInt256.ofNat 4 + UInt256.ofNat off.toNat) +
            UInt256.ofNat (32 * len.toNat)).toNat =
          4 + off.toNat + 32 * len.toNat := by
      apply uadd3_ofNat_toNat
      · norm_num [UInt256.size]
      · exact off.val.isLt
      · exact h32lenSmall
      · rw [show solcMaxU64 = 18446744073709551615 by rfl] at hoff
        norm_num [UInt256.size]
        omega
      · rw [show solcMaxU64 = 18446744073709551615 by rfl] at hoff hlen
        norm_num [UInt256.size]
        omega
    rw [uadd_toNat]
    change
      (((UInt256.ofNat 4 + UInt256.ofNat off.toNat) +
            UInt256.ofNat (32 * len.toNat)).toNat + (UInt256.ofNat 32).toNat) %
          UInt256.size =
        4 + (UInt256.ofNat off.toNat).toNat +
          32 * (UInt256.ofNat len.toNat).toNat + 32
    rw [h4off32len, ulit_toNat' 32 (by norm_num [UInt256.size]),
      ulit_toNat' off.toNat off.val.isLt, ulit_toNat' len.toNat len.val.isLt]
    apply Nat.mod_eq_of_lt
    rw [show solcMaxU64 = 18446744073709551615 by rfl] at hoff hlen
    norm_num [UInt256.size]
    omega
  by_contra hnot
  have hgt : UInt256.gt
      (((((⟨4⟩ : UInt256) + off) + UInt256.shiftLeft len ⟨5⟩) + ⟨32⟩))
      (UInt256.ofNat I.calldata.size) = ⟨1⟩ := by
    apply ugt_one
    rw [hleft, ulit_toNat' I.calldata.size hsize]
    omega
  rw [hend] at hgt
  have hnat := congrArg UInt256.toNat hgt
  change (0 : Nat) = 1 at hnat
  omega

theorem scratch_readNat_drop4_eq_calldataWord {I : ExecutionEnv} {headOff : Nat}
    (h : 4 + headOff + 32 ≤ I.calldata.size) :
    readNat? (List.drop 4 I.calldata.toList) headOff =
      some (calldataWord I.calldata (4 + headOff)).toNat := by
  unfold readNat? readWord? readBytes?
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hslice :
      (List.take 32 (List.drop headOff (List.drop 4 I.calldata.toList))).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  rw [if_pos hslice]
  rw [calldataWord]
  rw [List.drop_drop]
  rw [← decode_word_at_eq_any I.calldata (4 + headOff) h]
  rfl

theorem scratch_readNat_drop4_array_len_eq {I : ExecutionEnv} {off len : UInt256}
    (hoff : off.toNat ≤ solcMaxU64)
    (hbound : 4 + off.toNat + 32 ≤ I.calldata.size)
    (hlenWord :
      uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + off).toNat) 32) =
        len) :
    readNat? (List.drop 4 I.calldata.toList) off.toNat = some len.toNat := by
  have hread :=
    scratch_readNat_drop4_eq_calldataWord (I := I) (headOff := off.toNat)
      (by simpa [Nat.add_assoc] using hbound)
  have hstart : ((⟨4⟩ : UInt256) + off).toNat = 4 + off.toNat :=
    scratch_add4_word_toNat off hoff
  have hword : calldataWord I.calldata (4 + off.toNat) = len := by
    unfold calldataWord
    rw [← hstart]
    exact hlenWord
  rw [hread, hword]

theorem scratch_blindAuctionDecode_reveal_some_of_guards {I : ExecutionEnv}
    {valuesLen fakesLen secretsLen : UInt256}
    (hheadSize : 100 ≤ I.calldata.size)
    (hcalldataSign : I.calldata.size < 2 ^ 255)
    (hvaluesGt : UInt256.gt (revealValuesOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hvaluesStart :
      UInt256.slt (((⟨4⟩ : UInt256) + revealValuesOffsetWord I) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hvaluesLen :
      uInt256OfByteArray
        (I.calldata.readBytes (((⟨4⟩ : UInt256) + revealValuesOffsetWord I).toNat) 32) =
        valuesLen)
    (hvaluesLenMax : UInt256.gt valuesLen revealMaxU64 = ⟨0⟩)
    (hvaluesEnd :
      UInt256.gt
        ((((⟨4⟩ : UInt256) + revealValuesOffsetWord I) +
          UInt256.shiftLeft valuesLen ⟨5⟩) + ⟨32⟩)
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hfakesGt : UInt256.gt (revealFakesOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hfakesStart :
      UInt256.slt (((⟨4⟩ : UInt256) + revealFakesOffsetWord I) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hfakesLen :
      uInt256OfByteArray
        (I.calldata.readBytes (((⟨4⟩ : UInt256) + revealFakesOffsetWord I).toNat) 32) =
        fakesLen)
    (hfakesLenMax : UInt256.gt fakesLen revealMaxU64 = ⟨0⟩)
    (hfakesEnd :
      UInt256.gt
        ((((⟨4⟩ : UInt256) + revealFakesOffsetWord I) +
          UInt256.shiftLeft fakesLen ⟨5⟩) + ⟨32⟩)
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hsecretsGt : UInt256.gt (revealSecretsOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hsecretsStart :
      UInt256.slt (((⟨4⟩ : UInt256) + revealSecretsOffsetWord I) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hsecretsLen :
      uInt256OfByteArray
        (I.calldata.readBytes (((⟨4⟩ : UInt256) + revealSecretsOffsetWord I).toNat) 32) =
        secretsLen)
    (hsecretsLenMax : UInt256.gt secretsLen revealMaxU64 = ⟨0⟩)
    (hsecretsEnd :
      UInt256.gt
        ((((⟨4⟩ : UInt256) + revealSecretsOffsetWord I) +
          UInt256.shiftLeft secretsLen ⟨5⟩) + ⟨32⟩)
        (UInt256.ofNat I.calldata.size) = ⟨0⟩) :
    ∃ callargs,
      decodeCalldata (revealTransition.params.map Param.name)
        (transitionSignature revealTransition).paramTypes I.calldata = some callargs := by
  let args := List.drop 4 I.calldata.toList
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hargsLen : args.length = I.calldata.size - 4 := by
    dsimp [args]
    rw [List.length_drop, htlen]
  have hsize256 : I.calldata.size < UInt256.size := lt_size_of_lt_sign hcalldataSign
  have hvaluesOffLe := scratch_word_le_solcMax_of_ugt_zero hvaluesGt
  have hfakesOffLe := scratch_word_le_solcMax_of_ugt_zero hfakesGt
  have hsecretsOffLe := scratch_word_le_solcMax_of_ugt_zero hsecretsGt
  have hvaluesLenLe := scratch_word_le_solcMax_of_ugt_zero hvaluesLenMax
  have hfakesLenLe := scratch_word_le_solcMax_of_ugt_zero hfakesLenMax
  have hsecretsLenLe := scratch_word_le_solcMax_of_ugt_zero hsecretsLenMax
  have hvaluesStartBound :
      4 + (revealValuesOffsetWord I).toNat + 32 ≤ I.calldata.size := by
    have h := scratch_start_bound_of_slt_one
      (I := I) (off := revealValuesOffsetWord I) hcalldataSign hvaluesOffLe hvaluesStart
    omega
  have hfakesStartBound :
      4 + (revealFakesOffsetWord I).toNat + 32 ≤ I.calldata.size := by
    have h := scratch_start_bound_of_slt_one
      (I := I) (off := revealFakesOffsetWord I) hcalldataSign hfakesOffLe hfakesStart
    omega
  have hsecretsStartBound :
      4 + (revealSecretsOffsetWord I).toNat + 32 ≤ I.calldata.size := by
    have h := scratch_start_bound_of_slt_one
      (I := I) (off := revealSecretsOffsetWord I) hcalldataSign hsecretsOffLe
        hsecretsStart
    omega
  have hvaluesHead :
      readNat? args 0 = some (revealValuesOffsetWord I).toNat := by
    dsimp [args]
    simpa [revealValuesOffsetWord] using
      (scratch_readNat_drop4_eq_calldataWord (I := I) (headOff := 0) (by omega))
  have hfakesHead :
      readNat? args 32 = some (revealFakesOffsetWord I).toNat := by
    dsimp [args]
    simpa [revealFakesOffsetWord, Nat.add_assoc] using
      (scratch_readNat_drop4_eq_calldataWord (I := I) (headOff := 32) (by omega))
  have hsecretsHead :
      readNat? args 64 = some (revealSecretsOffsetWord I).toNat := by
    dsimp [args]
    simpa [revealSecretsOffsetWord, Nat.add_assoc] using
      (scratch_readNat_drop4_eq_calldataWord (I := I) (headOff := 64) (by omega))
  have hvaluesLenRead :
      readNat? args (revealValuesOffsetWord I).toNat = some valuesLen.toNat := by
    dsimp [args]
    exact scratch_readNat_drop4_array_len_eq
      (I := I) (off := revealValuesOffsetWord I) (len := valuesLen)
      hvaluesOffLe hvaluesStartBound hvaluesLen
  have hfakesLenRead :
      readNat? args (revealFakesOffsetWord I).toNat = some fakesLen.toNat := by
    dsimp [args]
    exact scratch_readNat_drop4_array_len_eq
      (I := I) (off := revealFakesOffsetWord I) (len := fakesLen)
      hfakesOffLe hfakesStartBound hfakesLen
  have hsecretsLenRead :
      readNat? args (revealSecretsOffsetWord I).toNat = some secretsLen.toNat := by
    dsimp [args]
    exact scratch_readNat_drop4_array_len_eq
      (I := I) (off := revealSecretsOffsetWord I) (len := secretsLen)
      hsecretsOffLe hsecretsStartBound hsecretsLen
  have hvaluesEndBound :
      (revealValuesOffsetWord I).toNat + 32 + 32 * valuesLen.toNat ≤ args.length := by
    have h := scratch_array_end_bound_of_ugt_zero
      (I := I) (off := revealValuesOffsetWord I) (len := valuesLen)
      hvaluesOffLe hvaluesLenLe hvaluesEnd hsize256
    rw [hargsLen]
    omega
  have hfakesEndBound :
      (revealFakesOffsetWord I).toNat + 32 + 32 * fakesLen.toNat ≤ args.length := by
    have h := scratch_array_end_bound_of_ugt_zero
      (I := I) (off := revealFakesOffsetWord I) (len := fakesLen)
      hfakesOffLe hfakesLenLe hfakesEnd hsize256
    rw [hargsLen]
    omega
  have hsecretsEndBound :
      (revealSecretsOffsetWord I).toNat + 32 + 32 * secretsLen.toNat ≤ args.length := by
    have h := scratch_array_end_bound_of_ugt_zero
      (I := I) (off := revealSecretsOffsetWord I) (len := secretsLen)
      hsecretsOffLe hsecretsLenLe hsecretsEnd hsize256
    rw [hargsLen]
    omega
  obtain ⟨values, hvaluesDecode, _hvaluesLength⟩ :=
    decodeABIValue_dynamicArray_uint256_exists
      (bytes := args) (start := (revealValuesOffsetWord I).toNat)
      (len := valuesLen.toNat) hvaluesLenRead
      (scratch_not_solcMax_lt_of_ugt_zero hvaluesLenMax) hvaluesEndBound
  obtain ⟨fakes, hfakesDecode, _hfakesLength⟩ :=
    decodeABIValue_dynamicArray_bool_exists
      (bytes := args) (start := (revealFakesOffsetWord I).toNat)
      (len := fakesLen.toNat) hfakesLenRead
      (scratch_not_solcMax_lt_of_ugt_zero hfakesLenMax) hfakesEndBound
  obtain ⟨secrets, hsecretsDecode, _hsecretsLength⟩ :=
    decodeABIValue_dynamicArray_bytes32_exists
      (bytes := args) (start := (revealSecretsOffsetWord I).toNat)
      (len := secretsLen.toNat) hsecretsLenRead
      (scratch_not_solcMax_lt_of_ugt_zero hsecretsLenMax) hsecretsEndBound
  let callargs : Store :=
    (((∅ : Store).insert "values" (.array values)).insert "fakes" (.array fakes)).insert
      "secrets" (.array secrets)
  refine ⟨callargs, ?_⟩
  change decodeCalldata ["values", "fakes", "secrets"]
    [.dynamicArray uint256, .dynamicArray boolTy, .dynamicArray bytes32] I.calldata =
      some callargs
  have hnotHugeFull :
      ¬([ABIType.dynamicArray uint256, ABIType.dynamicArray boolTy,
            ABIType.dynamicArray bytes32].any isDynamicABIType = true ∧
          2 ^ 255 ≤ I.calldata.toList.length) := by
    intro hhuge
    rcases hhuge with ⟨_, hhuge⟩
    rw [htlen] at hhuge
    omega
  have hnotHugeArgs :
      ¬([ABIType.dynamicArray uint256, ABIType.dynamicArray boolTy,
            ABIType.dynamicArray bytes32].isEmpty = false ∧
          2 ^ 255 ≤ (List.drop 4 I.calldata.toList).length) := by
    intro hhuge
    rcases hhuge with ⟨_, hhuge⟩
    rw [List.length_drop, htlen] at hhuge
    omega
  have hnotArgsShort : ¬ (List.drop 4 I.calldata.toList).length < 96 := by
    rw [List.length_drop, htlen]
    omega
  have hnotArgsShortSub : ¬ I.calldata.toList.length - 4 < 96 := by
    rw [htlen]
    omega
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg hnotHugeFull]
  rw [if_neg hnotHugeArgs]
  simp [decodeCalldata.decodeArgs, decodeABIValues?, abiTupleHeadSize?,
    isDynamicABIType, Option.bind, bind, args, hvaluesHead,
    scratch_not_solcMax_lt_of_ugt_zero hvaluesGt, hvaluesDecode, hfakesHead,
    scratch_not_solcMax_lt_of_ugt_zero hfakesGt, hfakesDecode, hsecretsHead,
    scratch_not_solcMax_lt_of_ugt_zero hsecretsGt, hsecretsDecode,
    decodeCalldata.insertValues, callargs, hnotArgsShortSub]

theorem scratch_blindAuctionRevealDecode1806_none_reverts
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : Nat}
    (rd : RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1806⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨413⟩, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hheadSize : 100 ≤ I.calldata.size)
    (hcalldataSign : I.calldata.size < 2 ^ 255)
    (hdecNone :
      decodeCalldata (revealTransition.params.map Param.name)
        (transitionSignature revealTransition).paramTypes I.calldata = none) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  by_cases hvaluesGt : UInt256.gt (revealValuesOffsetWord I) revealMaxU64 = ⟨1⟩
  · exact blindAuctionRevealX_decode_valuesOffset_revert
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hvaluesGt ⟨k, C, rd⟩
  · have hvaluesGt0 :
        UInt256.gt (revealValuesOffsetWord I) revealMaxU64 = ⟨0⟩ :=
      ugt_eq_zero_of_ne_one hvaluesGt
    obtain ⟨_, _, rd1713v⟩ :=
      blindAuctionRevealDecodeValuesCall1806_to_1713 rd hvaluesGt0
    by_cases hvaluesStart :
        UInt256.slt (((⟨4⟩ : UInt256) + revealValuesOffsetWord I) + ⟨31⟩)
          (UInt256.ofNat I.calldata.size) = ⟨1⟩
    · let valuesLen : UInt256 :=
        uInt256OfByteArray
          (I.calldata.readBytes (((⟨4⟩ : UInt256) + revealValuesOffsetWord I).toNat) 32)
      have hvaluesLen :
          uInt256OfByteArray
            (I.calldata.readBytes (((⟨4⟩ : UInt256) + revealValuesOffsetWord I).toNat) 32) =
            valuesLen := rfl
      by_cases hvaluesLenMax : UInt256.gt valuesLen revealMaxU64 = ⟨1⟩
      · exact RD.blindAuctionRevealDecodeArray1713_lengthRevert
          rd1713v hvaluesStart hvaluesLen hvaluesLenMax (by simp)
      · have hvaluesLenMax0 : UInt256.gt valuesLen revealMaxU64 = ⟨0⟩ :=
          ugt_eq_zero_of_ne_one hvaluesLenMax
        by_cases hvaluesEnd :
            UInt256.gt
              ((((⟨4⟩ : UInt256) + revealValuesOffsetWord I) +
                UInt256.shiftLeft valuesLen ⟨5⟩) + ⟨32⟩)
              (UInt256.ofNat I.calldata.size) = ⟨1⟩
        · exact RD.blindAuctionRevealDecodeArray1713_endRevert
            rd1713v hvaluesStart hvaluesLen hvaluesLenMax0 hvaluesEnd (by simp)
        · have hvaluesEnd0 :
              UInt256.gt
                ((((⟨4⟩ : UInt256) + revealValuesOffsetWord I) +
                  UInt256.shiftLeft valuesLen ⟨5⟩) + ⟨32⟩)
                (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
            ugt_eq_zero_of_ne_one hvaluesEnd
          obtain ⟨_, _, rd1840⟩ :=
            RD.blindAuctionRevealDecodeArray1713 rd1713v hvaluesStart hvaluesLen
              hvaluesLenMax0 hvaluesEnd0 (by jump_dest) (by simp)
          by_cases hfakesGt : UInt256.gt (revealFakesOffsetWord I) revealMaxU64 = ⟨1⟩
          · exact blindAuctionRevealDecodeFakesOffset1840_reverts rd1840 hfakesGt
          · have hfakesGt0 :
                UInt256.gt (revealFakesOffsetWord I) revealMaxU64 = ⟨0⟩ :=
              ugt_eq_zero_of_ne_one hfakesGt
            obtain ⟨_, _, rd1713f⟩ :=
              blindAuctionRevealDecodeFakesCall1840_to_1713 rd1840 hfakesGt0
            by_cases hfakesStart :
                UInt256.slt (((⟨4⟩ : UInt256) + revealFakesOffsetWord I) + ⟨31⟩)
                  (UInt256.ofNat I.calldata.size) = ⟨1⟩
            · let fakesLen : UInt256 :=
                uInt256OfByteArray
                  (I.calldata.readBytes
                    (((⟨4⟩ : UInt256) + revealFakesOffsetWord I).toNat) 32)
              have hfakesLen :
                  uInt256OfByteArray
                    (I.calldata.readBytes
                      (((⟨4⟩ : UInt256) + revealFakesOffsetWord I).toNat) 32) =
                    fakesLen := rfl
              by_cases hfakesLenMax : UInt256.gt fakesLen revealMaxU64 = ⟨1⟩
              · exact RD.blindAuctionRevealDecodeArray1713_lengthRevert
                  rd1713f hfakesStart hfakesLen hfakesLenMax (by simp)
              · have hfakesLenMax0 : UInt256.gt fakesLen revealMaxU64 = ⟨0⟩ :=
                  ugt_eq_zero_of_ne_one hfakesLenMax
                by_cases hfakesEnd :
                    UInt256.gt
                      ((((⟨4⟩ : UInt256) + revealFakesOffsetWord I) +
                        UInt256.shiftLeft fakesLen ⟨5⟩) + ⟨32⟩)
                      (UInt256.ofNat I.calldata.size) = ⟨1⟩
                · exact RD.blindAuctionRevealDecodeArray1713_endRevert
                    rd1713f hfakesStart hfakesLen hfakesLenMax0 hfakesEnd (by simp)
                · have hfakesEnd0 :
                      UInt256.gt
                        ((((⟨4⟩ : UInt256) + revealFakesOffsetWord I) +
                          UInt256.shiftLeft fakesLen ⟨5⟩) + ⟨32⟩)
                        (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
                    ugt_eq_zero_of_ne_one hfakesEnd
                  obtain ⟨_, _, rd1883⟩ :=
                    RD.blindAuctionRevealDecodeArray1713 rd1713f hfakesStart hfakesLen
                      hfakesLenMax0 hfakesEnd0 (by jump_dest) (by simp)
                  by_cases hsecretsGt :
                      UInt256.gt (revealSecretsOffsetWord I) revealMaxU64 = ⟨1⟩
                  · exact blindAuctionRevealDecodeSecretsOffset1883_reverts rd1883 hsecretsGt
                  · have hsecretsGt0 :
                        UInt256.gt (revealSecretsOffsetWord I) revealMaxU64 = ⟨0⟩ :=
                      ugt_eq_zero_of_ne_one hsecretsGt
                    obtain ⟨_, _, rd1713s⟩ :=
                      blindAuctionRevealDecodeSecretsCall1883_to_1713 rd1883 hsecretsGt0
                    by_cases hsecretsStart :
                        UInt256.slt
                          (((⟨4⟩ : UInt256) + revealSecretsOffsetWord I) + ⟨31⟩)
                          (UInt256.ofNat I.calldata.size) = ⟨1⟩
                    · let secretsLen : UInt256 :=
                        uInt256OfByteArray
                          (I.calldata.readBytes
                            (((⟨4⟩ : UInt256) + revealSecretsOffsetWord I).toNat) 32)
                      have hsecretsLen :
                          uInt256OfByteArray
                            (I.calldata.readBytes
                              (((⟨4⟩ : UInt256) + revealSecretsOffsetWord I).toNat) 32) =
                            secretsLen := rfl
                      by_cases hsecretsLenMax :
                          UInt256.gt secretsLen revealMaxU64 = ⟨1⟩
                      · exact RD.blindAuctionRevealDecodeArray1713_lengthRevert
                          rd1713s hsecretsStart hsecretsLen hsecretsLenMax (by simp)
                      · have hsecretsLenMax0 :
                            UInt256.gt secretsLen revealMaxU64 = ⟨0⟩ :=
                          ugt_eq_zero_of_ne_one hsecretsLenMax
                        by_cases hsecretsEnd :
                            UInt256.gt
                              ((((⟨4⟩ : UInt256) + revealSecretsOffsetWord I) +
                                UInt256.shiftLeft secretsLen ⟨5⟩) + ⟨32⟩)
                              (UInt256.ofNat I.calldata.size) = ⟨1⟩
                        · exact RD.blindAuctionRevealDecodeArray1713_endRevert
                            rd1713s hsecretsStart hsecretsLen hsecretsLenMax0 hsecretsEnd
                            (by simp)
                        · have hsecretsEnd0 :
                              UInt256.gt
                                ((((⟨4⟩ : UInt256) + revealSecretsOffsetWord I) +
                                  UInt256.shiftLeft secretsLen ⟨5⟩) + ⟨32⟩)
                                (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
                            ugt_eq_zero_of_ne_one hsecretsEnd
                          obtain ⟨callargs, hdecSome⟩ :=
                            scratch_blindAuctionDecode_reveal_some_of_guards
                              (I := I) (valuesLen := valuesLen) (fakesLen := fakesLen)
                              (secretsLen := secretsLen)
                              hheadSize hcalldataSign hvaluesGt0 hvaluesStart hvaluesLen
                              hvaluesLenMax0 hvaluesEnd0 hfakesGt0 hfakesStart hfakesLen
                              hfakesLenMax0 hfakesEnd0 hsecretsGt0 hsecretsStart hsecretsLen
                              hsecretsLenMax0 hsecretsEnd0
                          have hbad : (none : Option Store) = some callargs :=
                            hdecNone.symm.trans hdecSome
                          cases hbad
                    · have hsecretsStart0 :
                          UInt256.slt
                            (((⟨4⟩ : UInt256) + revealSecretsOffsetWord I) + ⟨31⟩)
                            (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
                        uslt_eq_zero_of_ne_one hsecretsStart
                      exact RD.blindAuctionRevealDecodeArray1713_startRevert rd1713s
                        hsecretsStart0 (by simp)
            · have hfakesStart0 :
                  UInt256.slt (((⟨4⟩ : UInt256) + revealFakesOffsetWord I) + ⟨31⟩)
                    (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
                uslt_eq_zero_of_ne_one hfakesStart
              exact RD.blindAuctionRevealDecodeArray1713_startRevert rd1713f hfakesStart0
                (by simp)
    · have hvaluesStart0 :
          UInt256.slt (((⟨4⟩ : UInt256) + revealValuesOffsetWord I) + ⟨31⟩)
            (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
        uslt_eq_zero_of_ne_one hvaluesStart
      exact RD.blindAuctionRevealDecodeArray1713_startRevert rd1713v hvaluesStart0 (by simp)

/-! ### Scratch placeBid source-side routine -/



end BlindAuction
