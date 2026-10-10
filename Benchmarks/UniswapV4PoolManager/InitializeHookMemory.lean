import Benchmarks.UniswapV4PoolManager.InitializeHookABI
import Benchmarks.UniswapV4PoolManager.PoolKeyEncodeMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def beforeInitializeSelectorWord : UInt256 :=
  UInt256.ofNat 99777755337597139797858614488041971895689843076832743791695422539262284791808
def afterInitializeSelectorWord : UInt256 :=
  UInt256.ofNat 50616461601953604499644185244379255888377203253588394779251873288349561126912
theorem beforeInitializeSelectorWord_bytes : beforeInitializeSelectorWord.toByteArray.extract 0 4 =
    beforeInitializeSelector := by decide +kernel
theorem afterInitializeSelectorWord_bytes : afterInitializeSelectorWord.toByteArray.extract 0 4 =
    afterInitializeSelector := by decide +kernel

def beforeInitializeMemory (mem : ByteArray) (free : UInt256) (sender : AccountAddress)
    (key : PoolKeyWords) (price : UInt256) : ByteArray :=
  writeWord (wordCallObjectMemory mem free beforeInitializeSelectorWord
    (accountWord sender :: poolKeyWordList key ++ [price])) 64 (free+⟨288⟩)
def afterInitializeMemory (mem : ByteArray) (free : UInt256) (sender : AccountAddress)
    (key : PoolKeyWords) (price tick : UInt256) : ByteArray :=
  writeWord (wordCallObjectMemory mem free afterInitializeSelectorWord
    (accountWord sender :: poolKeyWordList key ++ [price, tick])) 64 (free+⟨320⟩)

theorem beforeInitializeMemory_object (mem : ByteArray) (free : UInt256) (sender : AccountAddress)
    (key : PoolKeyWords) (price : UInt256) (hfree : 96 ≤ free.toNat) :
    BytesObjectView (beforeInitializeMemory mem free sender key price) free
      (beforeInitializePayload sender key price) := by
  have h := (wordCallObjectMemory_view mem free beforeInitializeSelectorWord
    (accountWord sender :: poolKeyWordList key ++ [price])).writeWord_before 64 (free+⟨288⟩) hfree
  simpa only [beforeInitializeSelectorWord_bytes, beforeInitializePayload] using h

theorem afterInitializeMemory_object (mem : ByteArray) (free : UInt256) (sender : AccountAddress)
    (key : PoolKeyWords) (price tick : UInt256) (hfree : 96 ≤ free.toNat) :
    BytesObjectView (afterInitializeMemory mem free sender key price tick) free
      (afterInitializePayload sender key price tick) := by
  have h := (wordCallObjectMemory_view mem free afterInitializeSelectorWord
    (accountWord sender :: poolKeyWordList key ++ [price, tick])).writeWord_before 64 (free+⟨320⟩) hfree
  simpa only [afterInitializeSelectorWord_bytes, afterInitializePayload] using h

theorem beforeInitializeMemory_free (mem : ByteArray) (free : UInt256) (sender : AccountAddress)
    (key : PoolKeyWords) (price : UInt256) :
    memLoad ⟨64⟩ (beforeInitializeMemory mem free sender key price) = free+⟨288⟩ :=
  writeWord_sparse_load_back _ ⟨64⟩ _
theorem afterInitializeMemory_free (mem : ByteArray) (free : UInt256) (sender : AccountAddress)
    (key : PoolKeyWords) (price tick : UInt256) :
    memLoad ⟨64⟩ (afterInitializeMemory mem free sender key price tick) = free+⟨320⟩ :=
  writeWord_sparse_load_back _ ⟨64⟩ _

theorem beforeInitializeMemory_key {mem : ByteArray} {keyPtr free : UInt256} {key : PoolKeyWords}
    (hv : PoolKeyView mem keyPtr key) (hb : keyPtr.toNat+160 ≤ free.toNat) (hlo : 96 ≤ keyPtr.toNat)
    (sender : AccountAddress) (price : UInt256) :
    PoolKeyView (beforeInitializeMemory mem free sender key price) keyPtr key := by
  refine ⟨(hv.slice.wordCallObject free _ _ ?_).writeWord 64 _ (.inr hlo), hv.fits⟩
  simpa only [wordBytes_size, poolKeyWordList, List.length_cons, List.length_nil] using hb

theorem afterInitializeMemory_key {mem : ByteArray} {keyPtr free : UInt256} {key : PoolKeyWords}
    (hv : PoolKeyView mem keyPtr key) (hb : keyPtr.toNat+160 ≤ free.toNat) (hlo : 96 ≤ keyPtr.toNat)
    (sender : AccountAddress) (price tick : UInt256) :
    PoolKeyView (afterInitializeMemory mem free sender key price tick) keyPtr key := by
  refine ⟨(hv.slice.wordCallObject free _ _ ?_).writeWord 64 _ (.inr hlo), hv.fits⟩
  simpa only [wordBytes_size, poolKeyWordList, List.length_cons, List.length_nil] using hb

end Benchmarks.UniswapV4PoolManager
