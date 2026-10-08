object "FixedBlue" {
  code {
    // A deterministic Blue-interface fixture, with no storage and no interest accrual.
    switch shr(224, calldataload(0))
    case 0x5c60e39a { // market(bytes32)
      mstore(0, 1000000000000000000)
      mstore(32, 1000000000000000000000000)
      mstore(64, 0)
      mstore(96, 0)
      mstore(128, 0)
      mstore(160, 0)
      return(0, 192)
    }
    case 0x2c3c9157 { // idToMarketParams(bytes32)
      mstore(0, 0x45804880de22913dafe09f4980848ece6ecbaf78)
      mstore(32, 0)
      mstore(64, 0)
      mstore(96, 0)
      mstore(128, 0)
      return(0, 160)
    }
    case 0x7784c685 { // extSloads(bytes32[]): one word per requested slot
      let n := calldataload(add(4, calldataload(4)))
      if gt(n, 30) { revert(0, 0) }
      mstore(0, 32)
      mstore(32, n)
      for { let i := 0 } lt(i, n) { i := add(i, 1) } {
        mstore(add(64, mul(i, 32)), 1000000000000000000)
      }
      return(0, add(64, mul(n, 32)))
    }
    case 0x93c52062 { // position(bytes32,address)
      mstore(0, 1000000000000000000)
      mstore(32, 0)
      mstore(64, 0)
      return(0, 96)
    }
    case 0xa99aad89 { // supply(MarketParams,uint256,uint256,address,bytes)
      let assets := calldataload(164)
      mstore(0, assets)
      mstore(32, mul(assets, 1000000))
      return(0, 64)
    }
    case 0x5c2bea49 { // withdraw(MarketParams,uint256,uint256,address,address)
      let assets := calldataload(164)
      let shares := calldataload(196)
      if iszero(assets) { assets := div(shares, 1000000) }
      if iszero(shares) { shares := mul(assets, 1000000) }
      mstore(0, assets)
      mstore(32, shares)
      return(0, 64)
    }
    case 0x151c1ade { return(0, 0) } // accrueInterest(MarketParams)
    default { revert(0, 0) }
  }
}
