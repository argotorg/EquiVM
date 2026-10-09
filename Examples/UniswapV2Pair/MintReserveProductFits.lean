import Examples.UniswapV2Pair.MintFeeSqrtSmall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

theorem mintFeeReserveProductNat_masked_lt (slot : UInt256) :
    (UInt256.land slot reserve112Mask).toNat *
      (UInt256.land (UInt256.div slot reserve112Shift) reserve112Mask).toNat < UInt256.size := by
  exact mintFeeReserveProductNat_lt_of_clean _ _
    (reserve112Mask_clean_of_lt _ (reserve112Word_lt _))
    (reserve112Mask_clean_of_lt _ (reserve112Word_lt _))

theorem mintFeeReserveProductNat_source_lt (evm : EVM.State) :
    mintFeeReserveProductNat (uniswapReserve0Word evm) (uniswapReserve1Word evm) <
      UInt256.size := by
  exact mintFeeReserveProductNat_masked_lt _

end UniswapV2Pair
