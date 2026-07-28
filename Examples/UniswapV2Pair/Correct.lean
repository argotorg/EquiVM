import Examples.UniswapV2Pair.Bytecode
import Examples.UniswapV2Pair.Dispatch
import Examples.UniswapV2Pair.Allowance
import Examples.UniswapV2Pair.Approve
import Examples.UniswapV2Pair.BalanceOf
import Examples.UniswapV2Pair.Burn
import Examples.UniswapV2Pair.Decimals
import Examples.UniswapV2Pair.DomainSeparator
import Examples.UniswapV2Pair.Factory
import Examples.UniswapV2Pair.GetReserves
import Examples.UniswapV2Pair.Initialize
import Examples.UniswapV2Pair.KLast
import Examples.UniswapV2Pair.MinimumLiquidity
import Examples.UniswapV2Pair.Mint
import Examples.UniswapV2Pair.Name
import Examples.UniswapV2Pair.Nonces
import Examples.UniswapV2Pair.PermitTypehash
import Examples.UniswapV2Pair.Permit
import Examples.UniswapV2Pair.Price0CumulativeLast
import Examples.UniswapV2Pair.Price1CumulativeLast
import Examples.UniswapV2Pair.Skim
import Examples.UniswapV2Pair.Swap
import Examples.UniswapV2Pair.Symbol
import Examples.UniswapV2Pair.SyncBody
import Examples.UniswapV2Pair.Token0
import Examples.UniswapV2Pair.Token1
import Examples.UniswapV2Pair.TotalSupply
import Examples.UniswapV2Pair.Transfer
import Examples.UniswapV2Pair.TransferFrom
import Examples.UniswapV2Pair.TransferFromFinite
import Examples.UniswapV2Pair.TransferFromSuccess
import Examples.UniswapV2Pair.TransferFromDecode
import Solm.Equiv

/-!
# UniswapV2Pair benchmark correctness stub

The source, ABI, optimized runtime bytecode, and Solm specification are present.  The equivalence
proof is intentionally left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

theorem uniswapV2PairCorrect :
    runtimeEquivalence config uniswapV2PairBytecode contract := by
  refine ⟨fun cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz : 4 ≤ I.calldata.size
    · by_cases hswap : selIs I ⟨#[0x02, 0x2c, 0x0d, 0x9f]⟩
      · exact uniswapSwapBody hcode hsize hperm hwv hswap (uniswapDispatchSwap hswap)
          hAccounts
      · by_cases hname : selIs I ⟨#[0x06, 0xfd, 0xde, 0x03]⟩
        · exact uniswapNameBody hcode hsize hwv hname (uniswapDispatchName hname)
            hAccounts
        · by_cases hgetReserves : selIs I ⟨#[0x09, 0x02, 0xf1, 0xac]⟩
          · exact uniswapGetReservesBody hcode hsize hwv hgetReserves
              (uniswapDispatchGetReserves hgetReserves) hAccounts
          · by_cases happrove : selIs I ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩
            · exact uniswapApproveBody hcode hsize hperm hwv happrove
                (uniswapDispatchApprove happrove) hAccounts
            · by_cases htoken0 : selIs I ⟨#[0x0d, 0xfe, 0x16, 0x81]⟩
              · exact uniswapToken0Body hcode hsize hwv htoken0
                  (uniswapDispatchToken0 htoken0) hAccounts
              · by_cases htotalSupply : selIs I ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩
                · exact uniswapTotalSupplyBody hcode hsize hwv htotalSupply
                    (uniswapDispatchTotalSupply htotalSupply) hAccounts
                · by_cases htransferFrom : selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩
                  · exact uniswapTransferFromBody hcode hsize hperm hwv htransferFrom
                      (uniswapDispatchTransferFrom htransferFrom) hAccounts
                  · by_cases hpermitTypehash : selIs I ⟨#[0x30, 0xad, 0xf8, 0x1f]⟩
                    · exact uniswapPermitTypehashBody hcode hsize hwv hpermitTypehash
                        (uniswapDispatchPermitTypehash hpermitTypehash) hAccounts
                    · by_cases hdecimals : selIs I ⟨#[0x31, 0x3c, 0xe5, 0x67]⟩
                      · exact uniswapDecimalsBody hcode hsize hwv hdecimals
                          (uniswapDispatchDecimals hdecimals) hAccounts
                      · by_cases hdomainSeparator : selIs I ⟨#[0x36, 0x44, 0xe5, 0x15]⟩
                        · exact uniswapDomainSeparatorBody hcode hsize hwv hdomainSeparator
                            (uniswapDispatchDomainSeparator hdomainSeparator) hAccounts
                        · by_cases hinitialize : selIs I ⟨#[0x48, 0x5c, 0xc9, 0x55]⟩
                          · exact uniswapInitializeBody hcode hsize hperm hwv hinitialize
                              (uniswapDispatchInitialize hinitialize) hAccounts
                          · by_cases hprice0 : selIs I ⟨#[0x59, 0x09, 0xc0, 0xd5]⟩
                            · exact uniswapPrice0CumulativeLastBody hcode hsize hwv hprice0
                                (uniswapDispatchPrice0CumulativeLast hprice0) hAccounts
                            · by_cases hprice1 : selIs I ⟨#[0x5a, 0x3d, 0x54, 0x93]⟩
                              · exact uniswapPrice1CumulativeLastBody hcode hsize hwv hprice1
                                  (uniswapDispatchPrice1CumulativeLast hprice1) hAccounts
                              · by_cases hmint : selIs I ⟨#[0x6a, 0x62, 0x78, 0x42]⟩
                                · exact uniswapMintBody hcode hsize hperm hwv hmint
                                    (uniswapDispatchMint hmint) hAccounts
                                · by_cases hbalanceOf : selIs I ⟨#[0x70, 0xa0, 0x82, 0x31]⟩
                                  · exact uniswapBalanceOfBody hcode hsize hwv hbalanceOf
                                      (uniswapDispatchBalanceOf hbalanceOf) hAccounts
                                  · by_cases hkLast : selIs I ⟨#[0x74, 0x64, 0xfc, 0x3d]⟩
                                    · exact uniswapKLastBody hcode hsize hwv hkLast
                                        (uniswapDispatchKLast hkLast) hAccounts
                                    · by_cases hnonces : selIs I ⟨#[0x7e, 0xce, 0xbe, 0x00]⟩
                                      · exact uniswapNoncesBody hcode hsize hwv hnonces
                                          (uniswapDispatchNonces hnonces) hAccounts
                                      · by_cases hburn : selIs I ⟨#[0x89, 0xaf, 0xcb, 0x44]⟩
                                        · exact uniswapBurnBody hcode hsize hperm hwv hburn
                                            (uniswapDispatchBurn hburn) hAccounts
                                        · by_cases hsymbol : selIs I ⟨#[0x95, 0xd8, 0x9b, 0x41]⟩
                                          · exact uniswapSymbolBody hcode hsize hwv hsymbol
                                              (uniswapDispatchSymbol hsymbol) hAccounts
                                          · by_cases htransfer : selIs I ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩
                                            · exact uniswapTransferBody hcode hsize hperm hwv
                                                htransfer (uniswapDispatchTransfer htransfer)
                                                hAccounts
                                            · by_cases hminimum : selIs I ⟨#[0xba, 0x9a, 0x7a, 0x56]⟩
                                              · exact uniswapMinimumLiquidityBody hcode hsize hwv
                                                  hminimum
                                                  (uniswapDispatchMinimumLiquidity hminimum)
                                                  hAccounts
                                              · by_cases hskim : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩
                                                · exact uniswapSkimBody hcode hsize hperm hwv hskim
                                                    (uniswapDispatchSkim hskim) hAccounts
                                                · by_cases hfactory : selIs I ⟨#[0xc4, 0x5a, 0x01, 0x55]⟩
                                                  · exact uniswapFactoryBody hcode hsize hwv hfactory
                                                      (uniswapDispatchFactory hfactory) hAccounts
                                                  · by_cases htoken1 : selIs I ⟨#[0xd2, 0x12, 0x20, 0xa7]⟩
                                                    · exact uniswapToken1Body hcode hsize hwv htoken1
                                                        (uniswapDispatchToken1 htoken1) hAccounts
                                                    · by_cases hpermit : selIs I ⟨#[0xd5, 0x05, 0xac, 0xcf]⟩
                                                      · exact uniswapPermitBody hcode hsize hperm hwv
                                                          hpermit (uniswapDispatchPermit hpermit)
                                                          hAccounts
                                                      · by_cases hallowance :
                                                            selIs I ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩
                                                        · exact uniswapAllowanceBody hcode hsize hwv
                                                            hallowance
                                                            (uniswapDispatchAllowance hallowance)
                                                            hAccounts
                                                        · by_cases hsync :
                                                              selIs I ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩
                                                          · exact uniswapSyncBody hcode hsize hperm hwv
                                                              hsync (uniswapDispatchSync hsync)
                                                              hAccounts
                                                          · refine uniswapNoDispatch hcode hsize hperm hwv ?_
                                                            intro i hi
                                                            interval_cases i
                                                            · simpa [selIs, uniswapSelBytes] using hswap
                                                            · simpa [selIs, uniswapSelBytes] using hname
                                                            · simpa [selIs, uniswapSelBytes] using hgetReserves
                                                            · simpa [selIs, uniswapSelBytes] using happrove
                                                            · simpa [selIs, uniswapSelBytes] using htoken0
                                                            · simpa [selIs, uniswapSelBytes] using htotalSupply
                                                            · simpa [selIs, uniswapSelBytes] using htransferFrom
                                                            · simpa [selIs, uniswapSelBytes] using hpermitTypehash
                                                            · simpa [selIs, uniswapSelBytes] using hdecimals
                                                            · simpa [selIs, uniswapSelBytes] using hdomainSeparator
                                                            · simpa [selIs, uniswapSelBytes] using hinitialize
                                                            · simpa [selIs, uniswapSelBytes] using hprice0
                                                            · simpa [selIs, uniswapSelBytes] using hprice1
                                                            · simpa [selIs, uniswapSelBytes] using hmint
                                                            · simpa [selIs, uniswapSelBytes] using hbalanceOf
                                                            · simpa [selIs, uniswapSelBytes] using hkLast
                                                            · simpa [selIs, uniswapSelBytes] using hnonces
                                                            · simpa [selIs, uniswapSelBytes] using hburn
                                                            · simpa [selIs, uniswapSelBytes] using hsymbol
                                                            · simpa [selIs, uniswapSelBytes] using htransfer
                                                            · simpa [selIs, uniswapSelBytes] using hminimum
                                                            · simpa [selIs, uniswapSelBytes] using hskim
                                                            · simpa [selIs, uniswapSelBytes] using hfactory
                                                            · simpa [selIs, uniswapSelBytes] using htoken1
                                                            · simpa [selIs, uniswapSelBytes] using hpermit
                                                            · simpa [selIs, uniswapSelBytes] using hallowance
                                                            · simpa [selIs, uniswapSelBytes] using hsync
    · exact uniswapShortRevert hcode hsize hperm hwv (by omega)
  · exact uniswapNonPayable hcode hwv

end UniswapV2Pair
