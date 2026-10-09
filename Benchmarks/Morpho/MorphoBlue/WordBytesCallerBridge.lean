import Benchmarks.Morpho.MorphoBlue.FinalizeVoid

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: a zero-value caller callback encoded as (uint256, bytes).
theorem wordBytesCallerBridge {code ee g s0 pc R aw out σ k C evm gasArg}
    {mem data : ByteArray} {ptr word srcOff len : UInt256}
    (cfg : Config) (name : String) (selector : UInt256)
    (hm : MorphoHeap mem ptr 0) (hs : SourceState s0 ee σ evm)
    (hlen : len.toNat ≤ solcMaxU64) (hsrc : srcOff.toNat + len.toNat ≤ ee.calldata.size)
    (hdata : ee.calldata.readWithPadding srcOff.toNat len.toNat = data)
    (hdataSize : data.size = len.toNat)
    (hencode : cfg.externalABI.encode? name [.int (Int.ofNat word.toNat), .bytes data] =
      some (wordBytesCalldata (selector.toByteArray.extract 0 4) word data))
    (hdec : decode code pc = some (.CALL, none)) (hov : R.length + 1 ≤ 1024)
    (h : RD code ee g s0 pc
      (gasArg :: UInt256.ofNat ee.source.val :: UInt256.ofNat 0 :: ptr ::
       UInt256.ofNat (100 + paddedSize len.toNat) :: ptr :: UInt256.ofNat 0 :: R)
      (wordBytesCallMem selector word ee.calldata mem srcOff.toNat ptr.toNat len.toNat) aw out σ k C) :
    ∃ (evm' : EVM.State) (σ' : AccountMap) (z : Bool) (result : ByteArray) (k' C' : Nat),
      typedCallViaEVM cfg evm evm.executionEnv.source name 0
        [.int (Int.ofNat word.toNat), .bytes data] (z, evm', result) ∧
      SourceState s0 ee σ' evm' ∧
      RD code ee g s0 (pc + UInt256.ofNat 1) ((if z then UInt256.ofNat 1 else UInt256.ofNat 0) :: R)
        (wordBytesCallMem selector word ee.calldata mem srcOff.toNat ptr.toNat len.toNat)
        (callActiveWords aw ptr (UInt256.ofNat (100 + paddedSize len.toNat)) ptr (UInt256.ofNat 0))
        result σ' k' C' ∧ result.size < 2 ^ 138 := by
  have hbound := paddedSize_le_add31 len.toNat
  have hfit : 100 + paddedSize len.toNat < UInt256.size := by
    norm_num [solcMaxU64, UInt256.size] at hlen ⊢; omega
  have hcd := wordBytesCallMem_read selector word ee.calldata mem data
    srcOff.toNat ptr.toNat len.toNat hsrc (by have hh := hm.gap; exact hh) hdata hdataSize
  have hsmall : (wordBytesCalldata (selector.toByteArray.extract 0 4) word data).size ≤ maxReturnDataSizeByGas := by
    simp only [wordBytesCalldata, ByteArray.size_append, wordBytesArguments_size, hdataSize]
    have hsel : (selector.toByteArray.extract 0 4).size = 4 := by
      rw [ByteArray.size_extract]; simp [toByteArray_size]
    rw [hsel]
    norm_num [solcMaxU64, maxReturnDataSizeByGas, maxReturnDataWordsByGas] at hlen ⊢
    omega
  obtain ⟨evm1, σ1, z, result, k1, C1, hcall, hs1, rd1, hout⟩ := zeroValueCallBridge
    (calldata := wordBytesCalldata (selector.toByteArray.extract 0 4) word data) h hs hdec
    (by rw [UInt256.toNat_ofNat_of_lt hfit]; exact hcd) hsmall hov
  have hmout : callOutputMem (wordBytesCallMem selector word ee.calldata mem srcOff.toNat ptr.toNat len.toNat)
      result ptr (UInt256.ofNat 0) =
      wordBytesCallMem selector word ee.calldata mem srcOff.toNat ptr.toNat len.toNat := callOutputMem_zero _ _ _
  rw [hmout] at rd1
  refine ⟨evm1, σ1, z, result, k1, C1, ⟨_, hencode, ?_⟩, hs1, rd1, hout⟩
  simpa only [accountAddress_roundtrip, hs.env] using hcall

-- LIBRARY CANDIDATE: callback encoding followed by finalizing a void return preserves the heap prefix.
theorem MorphoHeap.wordBytesCallRestored {mem : ByteArray} {ptr : UInt256}
    (hm : MorphoHeap mem ptr 0) (selector word : UInt256) (src : ByteArray) (srcOff len : Nat)
    (hsrc : srcOff + len ≤ src.size) :
    MorphoHeap (writeWord (wordBytesCallMem selector word src mem srcOff ptr.toNat len) 64 ptr) ptr 0 ∧
    MemoryPrefix mem (writeWord (wordBytesCallMem selector word src mem srcOff ptr.toNat len) 64 ptr) ptr.toNat := by
  have hm1 := hm.wordBytesCall selector word src srcOff len hsrc
  have hp := wordBytesCallMem_prefix selector word src mem srcOff ptr.toNat len hsrc
    (by have hh := hm.gap; exact hh)
  exact ⟨hm1.setFree.1, hp.trans hm1.setFree.2⟩

end Benchmarks.Morpho.MorphoBlue
