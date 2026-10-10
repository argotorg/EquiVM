import Benchmarks.UniswapV4PoolManager.BytesCallMemory
import Benchmarks.UniswapV4PoolManager.BytesReturnDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def unlockCallbackSelector : ByteArray := ⟨#[0x91, 0xdd, 0x73, 0x46]⟩
def unlockCallbackSelectorWord : UInt256 :=
  ⟨65976631833915796866350252598856538248815255225364396687512814530006169419776⟩

theorem unlockCallbackEncode (data : ByteArray) :
    config.externalABI.encode? "unlockCallback" [.bytes data] =
      some (unlockCallbackSelector ++ bytesReturnEncoding data) := encodeBytesCall _ _

theorem unlockCallbackCallMemory_encode (src base : ByteArray) (off srcAddr : Nat) (len : UInt256)
    (hb : base.size ≤ off+68) (hgap : off-base.size < USize.size)
    (hs : srcAddr+len.toNat ≤ src.size) :
    config.externalABI.encode? "unlockCallback" [.bytes (src.extract srcAddr (srcAddr+len.toNat))] =
      some ((bytesCallMemory src base off srcAddr unlockCallbackSelectorWord len).readWithPadding
        off (68+paddedSize len.toNat)) := by
  rw [bytesCallMemory_read _ _ _ _ _ _ hb hgap hs,
    show unlockCallbackSelectorWord.toByteArray.extract 0 4 = unlockCallbackSelector from by decide +kernel]
  exact unlockCallbackEncode _

theorem unlockCallbackDecode_ok {out : ByteArray} (hb : BytesReturnBounds out) :
    config.externalABI.decode? "unlockCallback" out = some [.bytes (bytesReturnPayload out)] := by
  change (decodeReturnValue? .bytes out).map (fun value => [value]) = _
  rw [decodeBytesReturn_ok hb]
  rfl

theorem unlockCallbackDecode_none {out : ByteArray} (hb : ¬BytesReturnBounds out) :
    config.externalABI.decode? "unlockCallback" out = none := by
  change (decodeReturnValue? .bytes out).map (fun value => [value]) = _
  rw [decodeBytesReturn_none hb]
  rfl

end Benchmarks.UniswapV4PoolManager
