import Examples.UniswapV2Pair.Common
import Mathlib.Tactic.IntervalCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## Dispatcher layout -/

/-- Root `GT` split after the standard solc selector load. -/
abbrev uniswapRootSplitPc : UInt256 := ⟨32⟩

/-- Low-half `GT` split reached from the root for selectors below `0x6a627842`. -/
abbrev uniswapLowSplitPc : UInt256 := ⟨250⟩

/-- Middle-low `GT` split for selectors at least `0x23b872dd` and below `0x6a627842`. -/
abbrev uniswapMidLowSplitPc : UInt256 := ⟨261⟩

/-- Lowest selector group jump destination for selectors below `0x23b872dd`. -/
abbrev uniswapLowestJumpdestPc : UInt256 := ⟨358⟩

/-- First arm in the lowest selector group (`swap`, `name`, ..., `totalSupply`). -/
abbrev uniswapLowestFirstArmPc : UInt256 := ⟨359⟩

/-- Middle-low selector group jump destination for selectors below `0x3644e515`. -/
abbrev uniswapMidLowJumpdestPc : UInt256 := ⟨320⟩

/-- First arm in the middle-low selector group (`transferFrom`, `PERMIT_TYPEHASH`, `decimals`). -/
abbrev uniswapMidLowFirstArmPc : UInt256 := ⟨321⟩

/-- First arm in the low-upper selector group (`DOMAIN_SEPARATOR`, `initialize`, prices). -/
abbrev uniswapLowUpperFirstArmPc : UInt256 := ⟨272⟩

/-- High-half split reached from the root for selectors at least `0x6a627842`. -/
abbrev uniswapHighSplitPc : UInt256 := ⟨43⟩

/-- Upper high-half split for selectors at least `0xba9a7a56`. -/
abbrev uniswapHighMidSplitPc : UInt256 := ⟨54⟩

/-- First arm in the high-upper selector group (`token1`, `permit`, `allowance`, `sync`). -/
abbrev uniswapHighUpperFirstArmPc : UInt256 := ⟨65⟩

/-- High-middle selector group jump destination. -/
abbrev uniswapHighMiddleJumpdestPc : UInt256 := ⟨113⟩

/-- First arm in the high-middle selector group (`MINIMUM_LIQUIDITY`, `skim`, `factory`). -/
abbrev uniswapHighMiddleFirstArmPc : UInt256 := ⟨114⟩

/-- High-lower selector split jump destination. -/
abbrev uniswapHighLowerJumpdestPc : UInt256 := ⟨151⟩

/-- High-lower selector split for selectors below `0xba9a7a56`. -/
abbrev uniswapHighLowerSplitPc : UInt256 := ⟨152⟩

/-- First arm in the high-lower selector group (`nonces`, `burn`, `symbol`, `transfer`). -/
abbrev uniswapHighLowerFirstArmPc : UInt256 := ⟨163⟩

/-- High-lowest selector group jump destination. -/
abbrev uniswapHighLowestJumpdestPc : UInt256 := ⟨211⟩

/-- First arm in the high-lowest selector group (`mint`, `balanceOf`, `kLast`). -/
abbrev uniswapHighLowestFirstArmPc : UInt256 := ⟨212⟩

set_option maxHeartbeats 1000000 in
/-- The lowest selector group contains six linear `EQ` arms. -/
theorem uniswapLowestArmsWellFormed :
    ∀ j, j ≤ 5 → armWellFormed uniswapV2PairBytecode
      (nthArmPc uniswapV2PairBytecode uniswapLowestFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
/-- The middle-low selector group contains three linear `EQ` arms. -/
theorem uniswapMidLowArmsWellFormed :
    ∀ j, j ≤ 2 → armWellFormed uniswapV2PairBytecode
      (nthArmPc uniswapV2PairBytecode uniswapMidLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
/-- The low-upper selector group contains four linear `EQ` arms. -/
theorem uniswapLowUpperArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed uniswapV2PairBytecode
      (nthArmPc uniswapV2PairBytecode uniswapLowUpperFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
/-- The high-upper selector group contains four linear `EQ` arms. -/
theorem uniswapHighUpperArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed uniswapV2PairBytecode
      (nthArmPc uniswapV2PairBytecode uniswapHighUpperFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
/-- The high-middle selector group contains three linear `EQ` arms. -/
theorem uniswapHighMiddleArmsWellFormed :
    ∀ j, j ≤ 2 → armWellFormed uniswapV2PairBytecode
      (nthArmPc uniswapV2PairBytecode uniswapHighMiddleFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
/-- The high-lower selector group contains four linear `EQ` arms. -/
theorem uniswapHighLowerArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed uniswapV2PairBytecode
      (nthArmPc uniswapV2PairBytecode uniswapHighLowerFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
/-- The high-lowest selector group contains three linear `EQ` arms. -/
theorem uniswapHighLowestArmsWellFormed :
    ∀ j, j ≤ 2 → armWellFormed uniswapV2PairBytecode
      (nthArmPc uniswapV2PairBytecode uniswapHighLowestFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

/-- The root selector split is `DUP1; PUSH4; GT; PUSH2; JUMPI`. -/
theorem uniswapRootSplitWellFormed :
    selectorSplitWellFormed uniswapV2PairBytecode uniswapRootSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

/-- The low selector split is `DUP1; PUSH4; GT; PUSH2; JUMPI`. -/
theorem uniswapLowSplitWellFormed :
    selectorSplitWellFormed uniswapV2PairBytecode uniswapLowSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

/-- The middle-low selector split is `DUP1; PUSH4; GT; PUSH2; JUMPI`. -/
theorem uniswapMidLowSplitWellFormed :
    selectorSplitWellFormed uniswapV2PairBytecode uniswapMidLowSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

/-- The high selector split is `DUP1; PUSH4; GT; PUSH2; JUMPI`. -/
theorem uniswapHighSplitWellFormed :
    selectorSplitWellFormed uniswapV2PairBytecode uniswapHighSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

/-- The high-middle selector split is `DUP1; PUSH4; GT; PUSH2; JUMPI`. -/
theorem uniswapHighMidSplitWellFormed :
    selectorSplitWellFormed uniswapV2PairBytecode uniswapHighMidSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

/-- The high-lower selector split is `DUP1; PUSH4; GT; PUSH2; JUMPI`. -/
theorem uniswapHighLowerSplitWellFormed :
    selectorSplitWellFormed uniswapV2PairBytecode uniswapHighLowerSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem uniswapSelWord_eq_of_beq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
    (hmatch : ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    uniswapSelWord I = sel := by
  exact solcSelectorWord_eq_of_beq I hsz c0 c1 c2 c3 sel hsel hmatch

/-- Uniswap V2 Pair selectors in `contract.transitions` order. -/
def uniswapSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x02, 0x2c, 0x0d, 0x9f]⟩
  | 1 => ⟨#[0x06, 0xfd, 0xde, 0x03]⟩
  | 2 => ⟨#[0x09, 0x02, 0xf1, 0xac]⟩
  | 3 => ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩
  | 4 => ⟨#[0x0d, 0xfe, 0x16, 0x81]⟩
  | 5 => ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩
  | 6 => ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩
  | 7 => ⟨#[0x30, 0xad, 0xf8, 0x1f]⟩
  | 8 => ⟨#[0x31, 0x3c, 0xe5, 0x67]⟩
  | 9 => ⟨#[0x36, 0x44, 0xe5, 0x15]⟩
  | 10 => ⟨#[0x48, 0x5c, 0xc9, 0x55]⟩
  | 11 => ⟨#[0x59, 0x09, 0xc0, 0xd5]⟩
  | 12 => ⟨#[0x5a, 0x3d, 0x54, 0x93]⟩
  | 13 => ⟨#[0x6a, 0x62, 0x78, 0x42]⟩
  | 14 => ⟨#[0x70, 0xa0, 0x82, 0x31]⟩
  | 15 => ⟨#[0x74, 0x64, 0xfc, 0x3d]⟩
  | 16 => ⟨#[0x7e, 0xce, 0xbe, 0x00]⟩
  | 17 => ⟨#[0x89, 0xaf, 0xcb, 0x44]⟩
  | 18 => ⟨#[0x95, 0xd8, 0x9b, 0x41]⟩
  | 19 => ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩
  | 20 => ⟨#[0xba, 0x9a, 0x7a, 0x56]⟩
  | 21 => ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩
  | 22 => ⟨#[0xc4, 0x5a, 0x01, 0x55]⟩
  | 23 => ⟨#[0xd2, 0x12, 0x20, 0xa7]⟩
  | 24 => ⟨#[0xd5, 0x05, 0xac, 0xcf]⟩
  | 25 => ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩
  | _ => ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩

/-! ## Solm dispatch routing

The generic `Reasoning.Dispatch` facts reduce `dispatchMsg` to the ordered transition list.  These
contract-local lemmas only attach Uniswap's selector byte facts to that generic machinery.
-/

attribute [local simp]
  uniswapSwapSelectorBytes
  uniswapNameSelectorBytes
  uniswapGetReservesSelectorBytes
  uniswapApproveSelectorBytes
  uniswapToken0SelectorBytes
  uniswapTotalSupplySelectorBytes
  uniswapTransferFromSelectorBytes
  uniswapPermitTypehashSelectorBytes
  uniswapDecimalsSelectorBytes
  uniswapDomainSeparatorSelectorBytes
  uniswapInitializeSelectorBytes
  uniswapPrice0CumulativeLastSelectorBytes
  uniswapPrice1CumulativeLastSelectorBytes
  uniswapMintSelectorBytes
  uniswapBalanceOfSelectorBytes
  uniswapKLastSelectorBytes
  uniswapNoncesSelectorBytes
  uniswapBurnSelectorBytes
  uniswapSymbolSelectorBytes
  uniswapTransferSelectorBytes
  uniswapMinimumLiquiditySelectorBytes
  uniswapSkimSelectorBytes
  uniswapFactorySelectorBytes
  uniswapToken1SelectorBytes
  uniswapPermitSelectorBytes
  uniswapAllowanceSelectorBytes
  uniswapSyncSelectorBytes

theorem uniswapDispatchSwap {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x02, 0x2c, 0x0d, 0x9f]⟩) :
    dispatchMsg contract I.calldata = some swapTransition := by
  have hcd : I.calldata.extract 0 4 = (⟨#[0x02, 0x2c, 0x0d, 0x9f]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  simp [dispatchMsg_eq_dispatchList, contract, dispatchList, selectorOf, hcd]
  native_decide

theorem uniswapDispatchName {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x06, 0xfd, 0xde, 0x03]⟩) :
    dispatchMsg contract I.calldata = some nameTransition := by
  have hcd : I.calldata.extract 0 4 = (⟨#[0x06, 0xfd, 0xde, 0x03]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  simp [dispatchMsg_eq_dispatchList, contract, dispatchList, selectorOf, hcd]
  native_decide

theorem uniswapDispatchGetReserves {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x09, 0x02, 0xf1, 0xac]⟩) :
    dispatchMsg contract I.calldata = some getReservesTransition := by
  have hcd : I.calldata.extract 0 4 = (⟨#[0x09, 0x02, 0xf1, 0xac]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  simp [dispatchMsg_eq_dispatchList, contract, dispatchList, selectorOf, hcd]
  native_decide

theorem uniswapDispatchApprove {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩) :
    dispatchMsg contract I.calldata = some approveTransition := by
  have hcd : I.calldata.extract 0 4 = (⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  simp [dispatchMsg_eq_dispatchList, contract, dispatchList, selectorOf, hcd]
  native_decide

theorem uniswapDispatchToken0 {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x0d, 0xfe, 0x16, 0x81]⟩) :
    dispatchMsg contract I.calldata = some token0Transition := by
  have hcd : I.calldata.extract 0 4 = (⟨#[0x0d, 0xfe, 0x16, 0x81]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  simp [dispatchMsg_eq_dispatchList, contract, dispatchList, selectorOf, hcd]
  native_decide

theorem uniswapDispatchTotalSupply {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩) :
    dispatchMsg contract I.calldata = some totalSupplyTransition := by
  have hcd : I.calldata.extract 0 4 = (⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  simp [dispatchMsg_eq_dispatchList, contract, dispatchList, selectorOf, hcd]
  native_decide

theorem uniswapDispatchTransferFrom {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩) :
    dispatchMsg contract I.calldata = some transferFromTransition := by
  have hcd : I.calldata.extract 0 4 = (⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  simp [dispatchMsg_eq_dispatchList, contract, dispatchList, selectorOf, hcd]
  native_decide

theorem uniswapDispatchPermitTypehash {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x30, 0xad, 0xf8, 0x1f]⟩) :
    dispatchMsg contract I.calldata = some permitTypehashTransition := by
  have hcd : I.calldata.extract 0 4 = (⟨#[0x30, 0xad, 0xf8, 0x1f]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  simp [dispatchMsg_eq_dispatchList, contract, dispatchList, selectorOf, hcd]
  native_decide

theorem uniswapDispatchDecimals {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x31, 0x3c, 0xe5, 0x67]⟩) :
    dispatchMsg contract I.calldata = some decimalsTransition := by
  have hcd : I.calldata.extract 0 4 = (⟨#[0x31, 0x3c, 0xe5, 0x67]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  simp [dispatchMsg_eq_dispatchList, contract, dispatchList, selectorOf, hcd]
  native_decide

theorem uniswapDispatchDomainSeparator {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x36, 0x44, 0xe5, 0x15]⟩) :
    dispatchMsg contract I.calldata = some domainSeparatorTransition := by
  have hcd : I.calldata.extract 0 4 = (⟨#[0x36, 0x44, 0xe5, 0x15]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  simp [dispatchMsg_eq_dispatchList, contract, dispatchList, selectorOf, hcd]
  native_decide

theorem uniswapDispatchInitialize {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x48, 0x5c, 0xc9, 0x55]⟩) :
    dispatchMsg contract I.calldata = some initializeTransition := by
  have hcd : I.calldata.extract 0 4 = (⟨#[0x48, 0x5c, 0xc9, 0x55]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  simp [dispatchMsg_eq_dispatchList, contract, dispatchList, selectorOf, hcd]
  native_decide

theorem uniswapDispatchPrice0CumulativeLast {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x59, 0x09, 0xc0, 0xd5]⟩) :
    dispatchMsg contract I.calldata = some price0CumulativeLastTransition := by
  have hcd : I.calldata.extract 0 4 = (⟨#[0x59, 0x09, 0xc0, 0xd5]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  simp [dispatchMsg_eq_dispatchList, contract, dispatchList, selectorOf, hcd]
  native_decide

theorem uniswapDispatchPrice1CumulativeLast {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x5a, 0x3d, 0x54, 0x93]⟩) :
    dispatchMsg contract I.calldata = some price1CumulativeLastTransition := by
  have hcd : I.calldata.extract 0 4 = (⟨#[0x5a, 0x3d, 0x54, 0x93]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  simp [dispatchMsg_eq_dispatchList, contract, dispatchList, selectorOf, hcd]
  native_decide

theorem uniswapDispatchMint {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x6a, 0x62, 0x78, 0x42]⟩) :
    dispatchMsg contract I.calldata = some mintTransition := by
  have hcd : I.calldata.extract 0 4 = (⟨#[0x6a, 0x62, 0x78, 0x42]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  simp [dispatchMsg_eq_dispatchList, contract, dispatchList, selectorOf, hcd]
  native_decide

theorem uniswapDispatchBalanceOf {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x70, 0xa0, 0x82, 0x31]⟩) :
    dispatchMsg contract I.calldata = some balanceOfTransition := by
  have hcd : I.calldata.extract 0 4 = (⟨#[0x70, 0xa0, 0x82, 0x31]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  simp [dispatchMsg_eq_dispatchList, contract, dispatchList, selectorOf, hcd]
  native_decide

theorem uniswapDispatchKLast {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x74, 0x64, 0xfc, 0x3d]⟩) :
    dispatchMsg contract I.calldata = some kLastTransition := by
  have hcd : I.calldata.extract 0 4 = (⟨#[0x74, 0x64, 0xfc, 0x3d]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  simp [dispatchMsg_eq_dispatchList, contract, dispatchList, selectorOf, hcd]
  native_decide

theorem uniswapDispatchNonces {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x7e, 0xce, 0xbe, 0x00]⟩) :
    dispatchMsg contract I.calldata = some noncesTransition := by
  have hcd : I.calldata.extract 0 4 = (⟨#[0x7e, 0xce, 0xbe, 0x00]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  simp [dispatchMsg_eq_dispatchList, contract, dispatchList, selectorOf, hcd]
  native_decide

theorem uniswapDispatchBurn {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x89, 0xaf, 0xcb, 0x44]⟩) :
    dispatchMsg contract I.calldata = some burnTransition := by
  have hcd : I.calldata.extract 0 4 = (⟨#[0x89, 0xaf, 0xcb, 0x44]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  simp [dispatchMsg_eq_dispatchList, contract, dispatchList, selectorOf, hcd]
  native_decide

theorem uniswapDispatchSymbol {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x95, 0xd8, 0x9b, 0x41]⟩) :
    dispatchMsg contract I.calldata = some symbolTransition := by
  have hcd : I.calldata.extract 0 4 = (⟨#[0x95, 0xd8, 0x9b, 0x41]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  simp [dispatchMsg_eq_dispatchList, contract, dispatchList, selectorOf, hcd]
  native_decide

theorem uniswapDispatchTransfer {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩) :
    dispatchMsg contract I.calldata = some transferTransition := by
  have hcd : I.calldata.extract 0 4 = (⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  simp [dispatchMsg_eq_dispatchList, contract, dispatchList, selectorOf, hcd]
  native_decide

theorem uniswapDispatchMinimumLiquidity {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xba, 0x9a, 0x7a, 0x56]⟩) :
    dispatchMsg contract I.calldata = some minimumLiquidityTransition := by
  have hcd : I.calldata.extract 0 4 = (⟨#[0xba, 0x9a, 0x7a, 0x56]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  simp [dispatchMsg_eq_dispatchList, contract, dispatchList, selectorOf, hcd]
  native_decide

theorem uniswapDispatchSkim {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩) :
    dispatchMsg contract I.calldata = some skimTransition := by
  have hcd : I.calldata.extract 0 4 = (⟨#[0xbc, 0x25, 0xcf, 0x77]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  simp [dispatchMsg_eq_dispatchList, contract, dispatchList, selectorOf, hcd]
  native_decide

theorem uniswapDispatchFactory {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xc4, 0x5a, 0x01, 0x55]⟩) :
    dispatchMsg contract I.calldata = some factoryTransition := by
  have hcd : I.calldata.extract 0 4 = (⟨#[0xc4, 0x5a, 0x01, 0x55]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  simp [dispatchMsg_eq_dispatchList, contract, dispatchList, selectorOf, hcd]
  native_decide

theorem uniswapDispatchToken1 {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xd2, 0x12, 0x20, 0xa7]⟩) :
    dispatchMsg contract I.calldata = some token1Transition := by
  have hcd : I.calldata.extract 0 4 = (⟨#[0xd2, 0x12, 0x20, 0xa7]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  simp [dispatchMsg_eq_dispatchList, contract, dispatchList, selectorOf, hcd]
  native_decide

theorem uniswapDispatchPermit {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xd5, 0x05, 0xac, 0xcf]⟩) :
    dispatchMsg contract I.calldata = some permitTransition := by
  have hcd : I.calldata.extract 0 4 = (⟨#[0xd5, 0x05, 0xac, 0xcf]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  simp [dispatchMsg_eq_dispatchList, contract, dispatchList, selectorOf, hcd]
  native_decide

theorem uniswapDispatchAllowance {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩) :
    dispatchMsg contract I.calldata = some allowanceTransition := by
  have hcd : I.calldata.extract 0 4 = (⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  simp [dispatchMsg_eq_dispatchList, contract, dispatchList, selectorOf, hcd]
  native_decide

theorem uniswapDispatchSync {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩) :
    dispatchMsg contract I.calldata = some syncTransition := by
  have hcd : I.calldata.extract 0 4 = (⟨#[0xff, 0xf6, 0xca, 0xe9]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  simp [dispatchMsg_eq_dispatchList, contract, dispatchList, selectorOf, hcd]
  native_decide

theorem uniswapDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList contract cd (by rfl)]
  change dispatchList
    [ swapTransition, nameTransition, getReservesTransition, approveTransition, token0Transition,
      totalSupplyTransition, transferFromTransition, permitTypehashTransition, decimalsTransition,
      domainSeparatorTransition, initializeTransition, price0CumulativeLastTransition,
      price1CumulativeLastTransition, mintTransition, balanceOfTransition, kLastTransition,
      noncesTransition, burnTransition, symbolTransition, transferTransition,
      minimumLiquidityTransition, skimTransition, factoryTransition, token1Transition,
      permitTransition, allowanceTransition, syncTransition ] cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp at ht
    rcases ht with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl
    · rw [selectorOf, uniswapSwapSelectorBytes]; rfl
    · rw [selectorOf, uniswapNameSelectorBytes]; rfl
    · rw [selectorOf, uniswapGetReservesSelectorBytes]; rfl
    · rw [selectorOf, uniswapApproveSelectorBytes]; rfl
    · rw [selectorOf, uniswapToken0SelectorBytes]; rfl
    · rw [selectorOf, uniswapTotalSupplySelectorBytes]; rfl
    · rw [selectorOf, uniswapTransferFromSelectorBytes]; rfl
    · rw [selectorOf, uniswapPermitTypehashSelectorBytes]; rfl
    · rw [selectorOf, uniswapDecimalsSelectorBytes]; rfl
    · rw [selectorOf, uniswapDomainSeparatorSelectorBytes]; rfl
    · rw [selectorOf, uniswapInitializeSelectorBytes]; rfl
    · rw [selectorOf, uniswapPrice0CumulativeLastSelectorBytes]; rfl
    · rw [selectorOf, uniswapPrice1CumulativeLastSelectorBytes]; rfl
    · rw [selectorOf, uniswapMintSelectorBytes]; rfl
    · rw [selectorOf, uniswapBalanceOfSelectorBytes]; rfl
    · rw [selectorOf, uniswapKLastSelectorBytes]; rfl
    · rw [selectorOf, uniswapNoncesSelectorBytes]; rfl
    · rw [selectorOf, uniswapBurnSelectorBytes]; rfl
    · rw [selectorOf, uniswapSymbolSelectorBytes]; rfl
    · rw [selectorOf, uniswapTransferSelectorBytes]; rfl
    · rw [selectorOf, uniswapMinimumLiquiditySelectorBytes]; rfl
    · rw [selectorOf, uniswapSkimSelectorBytes]; rfl
    · rw [selectorOf, uniswapFactorySelectorBytes]; rfl
    · rw [selectorOf, uniswapToken1SelectorBytes]; rfl
    · rw [selectorOf, uniswapPermitSelectorBytes]; rfl
    · rw [selectorOf, uniswapAllowanceSelectorBytes]; rfl
    · rw [selectorOf, uniswapSyncSelectorBytes]; rfl) h

theorem uniswapDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 27 → (uniswapSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg contract cd = none := by
  apply dispatchMsg_none_of_all_ne (contract := contract) (cd := cd) (hfallback := by rfl)
  intro t ht
  simp [contract] at ht
  rcases ht with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  · rw [selectorOf, uniswapSwapSelectorBytes]; simpa [uniswapSelBytes] using hnm 0 (by omega)
  · rw [selectorOf, uniswapNameSelectorBytes]; simpa [uniswapSelBytes] using hnm 1 (by omega)
  · rw [selectorOf, uniswapGetReservesSelectorBytes]
    simpa [uniswapSelBytes] using hnm 2 (by omega)
  · rw [selectorOf, uniswapApproveSelectorBytes]; simpa [uniswapSelBytes] using hnm 3 (by omega)
  · rw [selectorOf, uniswapToken0SelectorBytes]; simpa [uniswapSelBytes] using hnm 4 (by omega)
  · rw [selectorOf, uniswapTotalSupplySelectorBytes]
    simpa [uniswapSelBytes] using hnm 5 (by omega)
  · rw [selectorOf, uniswapTransferFromSelectorBytes]
    simpa [uniswapSelBytes] using hnm 6 (by omega)
  · rw [selectorOf, uniswapPermitTypehashSelectorBytes]
    simpa [uniswapSelBytes] using hnm 7 (by omega)
  · rw [selectorOf, uniswapDecimalsSelectorBytes]
    simpa [uniswapSelBytes] using hnm 8 (by omega)
  · rw [selectorOf, uniswapDomainSeparatorSelectorBytes]
    simpa [uniswapSelBytes] using hnm 9 (by omega)
  · rw [selectorOf, uniswapInitializeSelectorBytes]
    simpa [uniswapSelBytes] using hnm 10 (by omega)
  · rw [selectorOf, uniswapPrice0CumulativeLastSelectorBytes]
    simpa [uniswapSelBytes] using hnm 11 (by omega)
  · rw [selectorOf, uniswapPrice1CumulativeLastSelectorBytes]
    simpa [uniswapSelBytes] using hnm 12 (by omega)
  · rw [selectorOf, uniswapMintSelectorBytes]; simpa [uniswapSelBytes] using hnm 13 (by omega)
  · rw [selectorOf, uniswapBalanceOfSelectorBytes]
    simpa [uniswapSelBytes] using hnm 14 (by omega)
  · rw [selectorOf, uniswapKLastSelectorBytes]; simpa [uniswapSelBytes] using hnm 15 (by omega)
  · rw [selectorOf, uniswapNoncesSelectorBytes]; simpa [uniswapSelBytes] using hnm 16 (by omega)
  · rw [selectorOf, uniswapBurnSelectorBytes]; simpa [uniswapSelBytes] using hnm 17 (by omega)
  · rw [selectorOf, uniswapSymbolSelectorBytes]; simpa [uniswapSelBytes] using hnm 18 (by omega)
  · rw [selectorOf, uniswapTransferSelectorBytes]
    simpa [uniswapSelBytes] using hnm 19 (by omega)
  · rw [selectorOf, uniswapMinimumLiquiditySelectorBytes]
    simpa [uniswapSelBytes] using hnm 20 (by omega)
  · rw [selectorOf, uniswapSkimSelectorBytes]; simpa [uniswapSelBytes] using hnm 21 (by omega)
  · rw [selectorOf, uniswapFactorySelectorBytes]
    simpa [uniswapSelBytes] using hnm 22 (by omega)
  · rw [selectorOf, uniswapToken1SelectorBytes]
    simpa [uniswapSelBytes] using hnm 23 (by omega)
  · rw [selectorOf, uniswapPermitSelectorBytes]
    simpa [uniswapSelBytes] using hnm 24 (by omega)
  · rw [selectorOf, uniswapAllowanceSelectorBytes]
    simpa [uniswapSelBytes] using hnm 25 (by omega)
  · rw [selectorOf, uniswapSyncSelectorBytes]; simpa [uniswapSelBytes] using hnm 26 (by omega)

theorem uniswapBodyReverts_nonPayable (t : TransitionDecl) (ht : t ∈ contract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm locals t.body .reverted := by
  simp [contract] at ht
  rcases ht with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> exact bodyReverts_nonPayable h


end UniswapV2Pair
