import Examples.UniswapV2Pair.MintInternalMintRuntime

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

-- LIBRARY CANDIDATE: mapping-hash scratch writes preserve all word reads above byte 64.
theorem twoWordHashMem_read_above64 (key slot : UInt256) {mem : ByteArray} (offset : Nat)
    (hlo : 64 ≤ offset) (hin : offset + 32 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding offset 32 = mem.readWithPadding offset 32 := by
  unfold twoWordHashMem wordAt32Mem wordAt0Mem
  have hsize : (key.toByteArray.write 0 mem 0 32).size = mem.size :=
    toByteArray_write32_size_of_le mem key 0 mem.size mem.size rfl (by omega) (by omega)
  rw [write32_read_above _ _ 32 offset (by rw [toByteArray_size])
    (by rw [hsize]; omega) (by omega) (by rw [hsize]; omega),
    write32_read_above _ _ 0 offset (by rw [toByteArray_size]) (by omega) (by omega) hin]

theorem uniswapInternalMintBalanceHashMem_read96 (holder : UInt256) {mem : ByteArray}
    (hin : 128 ≤ mem.size) :
    (uniswapInternalMintBalanceHashMem holder mem).readWithPadding 96 32 =
      mem.readWithPadding 96 32 :=
  twoWordHashMem_read_above64 _ _ _ (by decide) hin

theorem uniswapInternalMintSuccessMem_read96 (holder value : UInt256) {mem : ByteArray}
    (hin : 160 ≤ mem.size) :
    (uniswapInternalMintLogMem value (uniswapInternalMintBalanceHashMem holder
      (uniswapInternalMintBalanceHashMem holder mem))).readWithPadding 96 32 =
      mem.readWithPadding 96 32 := by
  have hsize := uniswapInternalMintBalanceHashMem_size_of_ge64 holder (mem := mem) (by omega)
  have hsize2 := uniswapInternalMintDoubleBalanceHashMem_size_of_ge64 holder (mem := mem) (by omega)
  unfold uniswapInternalMintLogMem
  rw [write32_read_below _ _ 128 96 (by rw [toByteArray_size]) (by rw [hsize2]; omega) (by omega),
    uniswapInternalMintBalanceHashMem_read96 holder (by rw [hsize]; omega),
    uniswapInternalMintBalanceHashMem_read96 holder (by omega)]

theorem feeToStaticcallMem_read96 {mem : ByteArray} (out : ByteArray)
    (hmem : 160 ≤ mem.size) (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    (feeToStaticcallMem mem out).readWithPadding 96 32 = mem.readWithPadding 96 32 := by
  unfold feeToStaticcallMem
  rw [balanceOfThisStaticcallWriteLen_of_size_ge out hout32 houtSize,
    write32_read_below _ _ 128 96 hout32
      (by rw [feeToSelectorMem_size_of_ge160 hmem]; omega) (by omega)]
  unfold feeToSelectorMem
  rw [write32_read_below _ _ 128 96 (by rw [toByteArray_size]) (by omega) (by omega)]

end UniswapV2Pair
