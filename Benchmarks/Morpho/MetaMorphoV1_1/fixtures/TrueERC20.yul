object "TrueERC20" {
  code {
    switch shr(224, calldataload(0))
    case 0x313ce567 { mstore(0, 18) return(0, 32) }
    case 0x70a08231 { mstore(0, 1000000000000000000000000) return(0, 32) }
    default { mstore(0, 1) return(0, 32) }
  }
}
