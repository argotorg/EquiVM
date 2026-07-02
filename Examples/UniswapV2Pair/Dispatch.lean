import Examples.UniswapV2Pair.Common
import Mathlib.Tactic.IntervalCases

/-!
# UniswapV2Pair dispatcher reach slices

Small, bytecode-local dispatcher facts for the optimized binary selector tree.  These lemmas stop at
function body entries and are meant to feed the per-function `...BodyCore` lemmas from `Correct.lean`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

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

/-! ## Low selector branch reach -/

/-- Standard solc prologue/guards/selector load, stopping at the root selector split. -/
theorem uniswapReachRootSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
        uniswapRootSplitPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  simpa [uniswapRootSplitPc, uniswapSelWord] using
    solcLegacyDispatchReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (g := g) (code := uniswapV2PairBytecode)
      (bodyPc := (⟨18⟩ : UInt256)) (loadPc := (⟨26⟩ : UInt256))
      (firstPc := uniswapRootSplitPc) (guardTgt := (⟨16⟩ : UInt256))
      (revertTgt := (⟨425⟩ : UInt256)) (guardWidth := 2) (revertWidth := 2)
      (guardOp := .PUSH2) (revertOp := .PUSH2)
      hcode hwv hsz hsize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem uniswapX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have h12 := h0.push2 ⟨16⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.jumpiNT (by native_decide) (isZero_eq_zero_of_ne hwv)
      (by simp only [List.length]; omega)
  exact RD.uniswapPush1Dup1Revert0 h12 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length]; omega)

theorem uniswapX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  obtain ⟨_, _, h18⟩ := solcGuardCallvalueZero
    (ctgt := (⟨16⟩ : UInt256)) (opC := .PUSH2) (wC := 2)
    h0 hwv (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by jump_dest)
  have h425 := h18.push1 ⟨4⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.calldatasize (by native_decide) (by simp only [List.length]; omega)
    |>.lt (by native_decide) (by simp only [List.length]; omega)
    |>.push2 ⟨425⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.jumpiT (by native_decide) (lt_four_ne_zero_of_lt hsz) (by jump_dest)
      (by simp only [List.length]; omega)
    |>.jumpdest (by native_decide) (by simp only [List.length]; omega)
  exact RD.uniswapPush1Dup1Revert0 h425 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length]; omega)

/-- Reach the low-half split from the root split. -/
theorem uniswapReachLowSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
        uniswapLowSplitPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    uniswapReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h249 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      (armTgt uniswapV2PairBytecode uniswapRootSplitPc) [uniswapSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) :=
    RD.selectorSplitTakenAuto h32 uniswapRootSplitWellFormed hroot (by jump_dest) (by simp)
  have h250 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      uniswapLowSplitPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1) (C32 + 22 + 1) := by
    simpa [uniswapLowSplitPc, uniswapRootSplitPc, armTgt, pushAt] using
      h249.jumpdest (by decide) (by simp)
  exact ⟨_, _, h250⟩

/-- Reach the high-half split from the root split. -/
theorem uniswapReachHighSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) =
        ⟨0⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
        uniswapHighSplitPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    uniswapReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      uniswapHighSplitPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [uniswapHighSplitPc, uniswapRootSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h32 uniswapRootSplitWellFormed hroot (by simp)
  exact ⟨_, _, h43⟩

/-- Reach the first arm in Uniswap's lowest selector group. -/
theorem uniswapReachLowestFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) ≠ ⟨0⟩)
    (hlow :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapLowSplitPc) (uniswapSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
        uniswapLowestFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k250, C250, h250⟩ :=
    uniswapReachLowSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h358 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      (armTgt uniswapV2PairBytecode uniswapLowSplitPc) [uniswapSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) (k250 + 5)
        (C250 + 22) :=
    RD.selectorSplitTakenAuto h250 uniswapLowSplitWellFormed hlow (by jump_dest) (by simp)
  have h359 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      uniswapLowestFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k250 + 5 + 1) (C250 + 22 + 1) := by
    simpa [uniswapLowestFirstArmPc, uniswapLowestJumpdestPc, uniswapLowSplitPc, armTgt, pushAt]
      using h358.jumpdest (by decide) (by simp)
  exact ⟨_, _, h359⟩

/-- Reach the first arm in Uniswap's middle-low selector group. -/
theorem uniswapReachMidLowFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) ≠ ⟨0⟩)
    (hlow :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapLowSplitPc) (uniswapSelWord I) = ⟨0⟩)
    (hmidLow :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapMidLowSplitPc) (uniswapSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
        uniswapMidLowFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k250, C250, h250⟩ :=
    uniswapReachLowSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h261 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      uniswapMidLowSplitPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k250 + 5) (C250 + 22) := by
    simpa [uniswapMidLowSplitPc, uniswapLowSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h250 uniswapLowSplitWellFormed hlow (by simp)
  have h320 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      (armTgt uniswapV2PairBytecode uniswapMidLowSplitPc) [uniswapSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) (k250 + 5 + 5)
        (C250 + 22 + 22) :=
    RD.selectorSplitTakenAuto h261 uniswapMidLowSplitWellFormed hmidLow (by jump_dest) (by simp)
  have h321 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      uniswapMidLowFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k250 + 5 + 5 + 1) (C250 + 22 + 22 + 1) := by
    simpa [uniswapMidLowFirstArmPc, uniswapMidLowJumpdestPc, uniswapMidLowSplitPc, armTgt, pushAt]
      using h320.jumpdest (by decide) (by simp)
  exact ⟨_, _, h321⟩

/-- Reach the first arm in Uniswap's low-upper selector group. -/
theorem uniswapReachLowUpperFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) ≠ ⟨0⟩)
    (hlow :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapLowSplitPc) (uniswapSelWord I) = ⟨0⟩)
    (hmidLow :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapMidLowSplitPc) (uniswapSelWord I) =
        ⟨0⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
        uniswapLowUpperFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k250, C250, h250⟩ :=
    uniswapReachLowSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h261 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      uniswapMidLowSplitPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k250 + 5) (C250 + 22) := by
    simpa [uniswapMidLowSplitPc, uniswapLowSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h250 uniswapLowSplitWellFormed hlow (by simp)
  have h272 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      uniswapLowUpperFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k250 + 5 + 5) (C250 + 22 + 22) := by
    simpa [uniswapLowUpperFirstArmPc, uniswapMidLowSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h261 uniswapMidLowSplitWellFormed hmidLow (by simp)
  exact ⟨_, _, h272⟩

/-- Reach the first arm in Uniswap's high-upper selector group. -/
theorem uniswapReachHighUpperFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) =
        ⟨0⟩)
    (hhigh :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapHighSplitPc) (uniswapSelWord I) =
        ⟨0⟩)
    (hhighMid :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapHighMidSplitPc) (uniswapSelWord I) =
        ⟨0⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
        uniswapHighUpperFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k43, C43, h43⟩ :=
    uniswapReachHighSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h54 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      uniswapHighMidSplitPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k43 + 5) (C43 + 22) := by
    simpa [uniswapHighMidSplitPc, uniswapHighSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h43 uniswapHighSplitWellFormed hhigh (by simp)
  have h65 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      uniswapHighUpperFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k43 + 5 + 5) (C43 + 22 + 22) := by
    simpa [uniswapHighUpperFirstArmPc, uniswapHighMidSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h54 uniswapHighMidSplitWellFormed hhighMid (by simp)
  exact ⟨_, _, h65⟩

/-- Reach the first arm in Uniswap's high-middle selector group. -/
theorem uniswapReachHighMiddleFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) =
        ⟨0⟩)
    (hhigh :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapHighSplitPc) (uniswapSelWord I) =
        ⟨0⟩)
    (hhighMid :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapHighMidSplitPc) (uniswapSelWord I) ≠
        ⟨0⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
        uniswapHighMiddleFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k43, C43, h43⟩ :=
    uniswapReachHighSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h54 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      uniswapHighMidSplitPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k43 + 5) (C43 + 22) := by
    simpa [uniswapHighMidSplitPc, uniswapHighSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h43 uniswapHighSplitWellFormed hhigh (by simp)
  have h113 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      (armTgt uniswapV2PairBytecode uniswapHighMidSplitPc) [uniswapSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) (k43 + 5 + 5)
        (C43 + 22 + 22) :=
    RD.selectorSplitTakenAuto h54 uniswapHighMidSplitWellFormed hhighMid (by jump_dest) (by simp)
  have h114 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      uniswapHighMiddleFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k43 + 5 + 5 + 1) (C43 + 22 + 22 + 1) := by
    simpa [uniswapHighMiddleFirstArmPc, uniswapHighMiddleJumpdestPc, uniswapHighMidSplitPc,
      armTgt, pushAt] using h113.jumpdest (by decide) (by simp)
  exact ⟨_, _, h114⟩

/-- Reach the high-lower split in Uniswap's high selector branch. -/
theorem uniswapReachHighLowerSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) =
        ⟨0⟩)
    (hhigh :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapHighSplitPc) (uniswapSelWord I) ≠
        ⟨0⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
        uniswapHighLowerSplitPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k43, C43, h43⟩ :=
    uniswapReachHighSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h151 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      (armTgt uniswapV2PairBytecode uniswapHighSplitPc) [uniswapSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) (k43 + 5) (C43 + 22) :=
    RD.selectorSplitTakenAuto h43 uniswapHighSplitWellFormed hhigh (by jump_dest) (by simp)
  have h152 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      uniswapHighLowerSplitPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k43 + 5 + 1) (C43 + 22 + 1) := by
    simpa [uniswapHighLowerSplitPc, uniswapHighLowerJumpdestPc, uniswapHighSplitPc, armTgt,
      pushAt] using h151.jumpdest (by decide) (by simp)
  exact ⟨_, _, h152⟩

/-- Reach the first arm in Uniswap's high-lower selector group. -/
theorem uniswapReachHighLowerFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) =
        ⟨0⟩)
    (hhigh :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapHighSplitPc) (uniswapSelWord I) ≠
        ⟨0⟩)
    (hlower :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapHighLowerSplitPc) (uniswapSelWord I) =
        ⟨0⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
        uniswapHighLowerFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k152, C152, h152⟩ :=
    uniswapReachHighLowerSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh
  have h163 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      uniswapHighLowerFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k152 + 5) (C152 + 22) := by
    simpa [uniswapHighLowerFirstArmPc, uniswapHighLowerSplitPc, selArmNextPc,
      armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h152 uniswapHighLowerSplitWellFormed hlower (by simp)
  exact ⟨_, _, h163⟩

/-- Reach the first arm in Uniswap's high-lowest selector group. -/
theorem uniswapReachHighLowestFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) =
        ⟨0⟩)
    (hhigh :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapHighSplitPc) (uniswapSelWord I) ≠
        ⟨0⟩)
    (hlower :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapHighLowerSplitPc) (uniswapSelWord I) ≠
        ⟨0⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
        uniswapHighLowestFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k152, C152, h152⟩ :=
    uniswapReachHighLowerSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh
  have h211 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      (armTgt uniswapV2PairBytecode uniswapHighLowerSplitPc) [uniswapSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) (k152 + 5) (C152 + 22) :=
    RD.selectorSplitTakenAuto h152 uniswapHighLowerSplitWellFormed hlower (by jump_dest) (by simp)
  have h212 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      uniswapHighLowestFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k152 + 5 + 1) (C152 + 22 + 1) := by
    simpa [uniswapHighLowestFirstArmPc, uniswapHighLowestJumpdestPc, uniswapHighLowerSplitPc,
      armTgt, pushAt] using h211.jumpdest (by decide) (by simp)
  exact ⟨_, _, h212⟩

theorem uniswapJumpToNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    {pc : UInt256} {k C : ℕ}
    (h : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) pc
      [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hpush : decode uniswapV2PairBytecode pc = some (.Push .PUSH2, some (⟨425⟩, 2)))
    (hjump : decode uniswapV2PairBytecode (pc + UInt256.ofNat 3) = some (.JUMP, .none)) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h425 := h.push2 ⟨425⟩ hpush (by simp only [List.length_singleton]; omega)
    |>.jump hjump (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  exact RD.uniswapPush1Dup1Revert0 h425 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_singleton]; omega)

theorem uniswapX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 27 → (uniswapSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hselectorNoMatch (i : ℕ) (hi : i < 27) (c0 c1 c2 c3 : UInt8) (sel : UInt256)
      (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
      (hbytes : uniswapSelBytes i = (⟨#[c0, c1, c2, c3]⟩ : ByteArray)) :
      UInt256.eq sel (uniswapSelWord I) = ⟨0⟩ := by
    dsimp [uniswapSelWord]
    rw [evmSelectorDecode hsz c0 c1 c2 c3 sel hsel]
    have hno := hnm i hi
    rw [hbytes] at hno
    simp [hno]
  have heqLowest : ∀ j, j < 6 →
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapLowestFirstArmPc j))
        (uniswapSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact hselectorNoMatch 0 (by omega) 0x02 0x2c 0x0d 0x9f _ (by native_decide) rfl
    · exact hselectorNoMatch 1 (by omega) 0x06 0xfd 0xde 0x03 _ (by native_decide) rfl
    · exact hselectorNoMatch 2 (by omega) 0x09 0x02 0xf1 0xac _ (by native_decide) rfl
    · exact hselectorNoMatch 3 (by omega) 0x09 0x5e 0xa7 0xb3 _ (by native_decide) rfl
    · exact hselectorNoMatch 4 (by omega) 0x0d 0xfe 0x16 0x81 _ (by native_decide) rfl
    · exact hselectorNoMatch 5 (by omega) 0x18 0x16 0x0d 0xdd _ (by native_decide) rfl
  have heqMidLow : ∀ j, j < 3 →
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapMidLowFirstArmPc j))
        (uniswapSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact hselectorNoMatch 6 (by omega) 0x23 0xb8 0x72 0xdd _ (by native_decide) rfl
    · exact hselectorNoMatch 7 (by omega) 0x30 0xad 0xf8 0x1f _ (by native_decide) rfl
    · exact hselectorNoMatch 8 (by omega) 0x31 0x3c 0xe5 0x67 _ (by native_decide) rfl
  have heqLowUpper : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapLowUpperFirstArmPc j))
        (uniswapSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact hselectorNoMatch 9 (by omega) 0x36 0x44 0xe5 0x15 _ (by native_decide) rfl
    · exact hselectorNoMatch 10 (by omega) 0x48 0x5c 0xc9 0x55 _ (by native_decide) rfl
    · exact hselectorNoMatch 11 (by omega) 0x59 0x09 0xc0 0xd5 _ (by native_decide) rfl
    · exact hselectorNoMatch 12 (by omega) 0x5a 0x3d 0x54 0x93 _ (by native_decide) rfl
  have heqHighUpper : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapHighUpperFirstArmPc j))
        (uniswapSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact hselectorNoMatch 23 (by omega) 0xd2 0x12 0x20 0xa7 _ (by native_decide) rfl
    · exact hselectorNoMatch 24 (by omega) 0xd5 0x05 0xac 0xcf _ (by native_decide) rfl
    · exact hselectorNoMatch 25 (by omega) 0xdd 0x62 0xed 0x3e _ (by native_decide) rfl
    · exact hselectorNoMatch 26 (by omega) 0xff 0xf6 0xca 0xe9 _ (by native_decide) rfl
  have heqHighMiddle : ∀ j, j < 3 →
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapHighMiddleFirstArmPc j))
        (uniswapSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact hselectorNoMatch 20 (by omega) 0xba 0x9a 0x7a 0x56 _ (by native_decide) rfl
    · exact hselectorNoMatch 21 (by omega) 0xbc 0x25 0xcf 0x77 _ (by native_decide) rfl
    · exact hselectorNoMatch 22 (by omega) 0xc4 0x5a 0x01 0x55 _ (by native_decide) rfl
  have heqHighLower : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapHighLowerFirstArmPc j))
        (uniswapSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact hselectorNoMatch 16 (by omega) 0x7e 0xce 0xbe 0x00 _ (by native_decide) rfl
    · exact hselectorNoMatch 17 (by omega) 0x89 0xaf 0xcb 0x44 _ (by native_decide) rfl
    · exact hselectorNoMatch 18 (by omega) 0x95 0xd8 0x9b 0x41 _ (by native_decide) rfl
    · exact hselectorNoMatch 19 (by omega) 0xa9 0x05 0x9c 0xbb _ (by native_decide) rfl
  have heqHighLowest : ∀ j, j < 3 →
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapHighLowestFirstArmPc j))
        (uniswapSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact hselectorNoMatch 13 (by omega) 0x6a 0x62 0x78 0x42 _ (by native_decide) rfl
    · exact hselectorNoMatch 14 (by omega) 0x70 0xa0 0x82 0x31 _ (by native_decide) rfl
    · exact hselectorNoMatch 15 (by omega) 0x74 0x64 0xfc 0x3d _ (by native_decide) rfl
  by_cases hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) =
        ⟨0⟩
  · by_cases hhigh :
        UInt256.gt (armSelNat uniswapV2PairBytecode uniswapHighSplitPc) (uniswapSelWord I) =
          ⟨0⟩
    · by_cases hhighMid :
          UInt256.gt (armSelNat uniswapV2PairBytecode uniswapHighMidSplitPc) (uniswapSelWord I) =
            ⟨0⟩
      · obtain ⟨_, _, h65⟩ := uniswapReachHighUpperFirstArm (cA := cA) (gh := gh)
          (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hwv hsz hsize hroot hhigh hhighMid
        have h109 := h65
          |>.selectorArmNotTakenAuto (uniswapHighUpperArmsWellFormed 0 (by omega))
              (heqHighUpper 0 (by omega)) (by simp)
          |>.selectorArmNotTakenAuto (uniswapHighUpperArmsWellFormed 1 (by omega))
              (heqHighUpper 1 (by omega)) (by simp)
          |>.selectorArmNotTakenAuto (uniswapHighUpperArmsWellFormed 2 (by omega))
              (heqHighUpper 2 (by omega)) (by simp)
          |>.selectorArmNotTakenAuto (uniswapHighUpperArmsWellFormed 3 (by omega))
              (heqHighUpper 3 (by omega)) (by simp)
        exact uniswapJumpToNoMatchRevert h109 (by native_decide) (by native_decide)
      · obtain ⟨_, _, h114⟩ := uniswapReachHighMiddleFirstArm (cA := cA) (gh := gh)
          (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hwv hsz hsize hroot hhigh hhighMid
        have h147 := h114
          |>.selectorArmNotTakenAuto (uniswapHighMiddleArmsWellFormed 0 (by omega))
              (heqHighMiddle 0 (by omega)) (by simp)
          |>.selectorArmNotTakenAuto (uniswapHighMiddleArmsWellFormed 1 (by omega))
              (heqHighMiddle 1 (by omega)) (by simp)
          |>.selectorArmNotTakenAuto (uniswapHighMiddleArmsWellFormed 2 (by omega))
              (heqHighMiddle 2 (by omega)) (by simp)
        exact uniswapJumpToNoMatchRevert h147 (by native_decide) (by native_decide)
    · by_cases hlower :
        UInt256.gt (armSelNat uniswapV2PairBytecode uniswapHighLowerSplitPc) (uniswapSelWord I) =
          ⟨0⟩
      · obtain ⟨_, _, h163⟩ := uniswapReachHighLowerFirstArm (cA := cA) (gh := gh)
          (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hwv hsz hsize hroot hhigh hlower
        have h207 := h163
          |>.selectorArmNotTakenAuto (uniswapHighLowerArmsWellFormed 0 (by omega))
              (heqHighLower 0 (by omega)) (by simp)
          |>.selectorArmNotTakenAuto (uniswapHighLowerArmsWellFormed 1 (by omega))
              (heqHighLower 1 (by omega)) (by simp)
          |>.selectorArmNotTakenAuto (uniswapHighLowerArmsWellFormed 2 (by omega))
              (heqHighLower 2 (by omega)) (by simp)
          |>.selectorArmNotTakenAuto (uniswapHighLowerArmsWellFormed 3 (by omega))
              (heqHighLower 3 (by omega)) (by simp)
        exact uniswapJumpToNoMatchRevert h207 (by native_decide) (by native_decide)
      · obtain ⟨_, _, h212⟩ := uniswapReachHighLowestFirstArm (cA := cA) (gh := gh)
          (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hwv hsz hsize hroot hhigh hlower
        have h245 := h212
          |>.selectorArmNotTakenAuto (uniswapHighLowestArmsWellFormed 0 (by omega))
              (heqHighLowest 0 (by omega)) (by simp)
          |>.selectorArmNotTakenAuto (uniswapHighLowestArmsWellFormed 1 (by omega))
              (heqHighLowest 1 (by omega)) (by simp)
          |>.selectorArmNotTakenAuto (uniswapHighLowestArmsWellFormed 2 (by omega))
              (heqHighLowest 2 (by omega)) (by simp)
        exact uniswapJumpToNoMatchRevert h245 (by native_decide) (by native_decide)
  · by_cases hlow :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapLowSplitPc) (uniswapSelWord I) =
        ⟨0⟩
    · by_cases hmidLow :
        UInt256.gt (armSelNat uniswapV2PairBytecode uniswapMidLowSplitPc) (uniswapSelWord I) =
          ⟨0⟩
      · obtain ⟨_, _, h272⟩ := uniswapReachLowUpperFirstArm (cA := cA) (gh := gh)
          (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hwv hsz hsize hroot hlow hmidLow
        have h316 := h272
          |>.selectorArmNotTakenAuto (uniswapLowUpperArmsWellFormed 0 (by omega))
              (heqLowUpper 0 (by omega)) (by simp)
          |>.selectorArmNotTakenAuto (uniswapLowUpperArmsWellFormed 1 (by omega))
              (heqLowUpper 1 (by omega)) (by simp)
          |>.selectorArmNotTakenAuto (uniswapLowUpperArmsWellFormed 2 (by omega))
              (heqLowUpper 2 (by omega)) (by simp)
          |>.selectorArmNotTakenAuto (uniswapLowUpperArmsWellFormed 3 (by omega))
              (heqLowUpper 3 (by omega)) (by simp)
        exact uniswapJumpToNoMatchRevert h316 (by native_decide) (by native_decide)
      · obtain ⟨_, _, h321⟩ := uniswapReachMidLowFirstArm (cA := cA) (gh := gh)
          (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hwv hsz hsize hroot hlow hmidLow
        have h354 := h321
          |>.selectorArmNotTakenAuto (uniswapMidLowArmsWellFormed 0 (by omega))
              (heqMidLow 0 (by omega)) (by simp)
          |>.selectorArmNotTakenAuto (uniswapMidLowArmsWellFormed 1 (by omega))
              (heqMidLow 1 (by omega)) (by simp)
          |>.selectorArmNotTakenAuto (uniswapMidLowArmsWellFormed 2 (by omega))
              (heqMidLow 2 (by omega)) (by simp)
        exact uniswapJumpToNoMatchRevert h354 (by native_decide) (by native_decide)
    · obtain ⟨_, _, h359⟩ := uniswapReachLowestFirstArm (cA := cA) (gh := gh)
        (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hwv hsz hsize hroot hlow
      have h425 := h359
        |>.selectorArmNotTakenAuto (uniswapLowestArmsWellFormed 0 (by omega))
            (heqLowest 0 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (uniswapLowestArmsWellFormed 1 (by omega))
            (heqLowest 1 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (uniswapLowestArmsWellFormed 2 (by omega))
            (heqLowest 2 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (uniswapLowestArmsWellFormed 3 (by omega))
            (heqLowest 3 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (uniswapLowestArmsWellFormed 4 (by omega))
            (heqLowest 4 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (uniswapLowestArmsWellFormed 5 (by omega))
            (heqLowest 5 (by omega)) (by simp)
      have h426 := h425.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
      exact RD.uniswapPush1Dup1Revert0 h426 (by native_decide) (by native_decide)
        (by native_decide) (by simp only [List.length_singleton]; omega)

theorem uniswapNonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (uniswapX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
    fun _ _ hrev => by
      by_cases hdisp : dispatchMsg contract I.calldata = none
      · exact reEquiv_noDispatch hdisp hrev
      · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
        have htmem : t ∈ contract.transitions := by
          rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl)] at ht
          exact dispatchList_some_mem ht
        by_cases hdec : decodeCalldataWithMode config.abiDecodeMode (t.params.map Param.name)
            (transitionSignature t).paramTypes I.calldata = none
        · exact reEquiv_decodingFailed ht hdec hrev
        · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
          exact reEquiv_execution ht hca
            (uniswapBodyReverts_nonPayable t htmem
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

theorem uniswapShortRevert {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (uniswapX_short (g := Sat256.ofUInt256 g) hcode hwv hsz).reEquivNoDispatch hcode
    (uniswapDispatch_none_short hsz)

theorem uniswapNoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 27 → (uniswapSelBytes i == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (uniswapX_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm)
      |>.reEquivNoDispatch hcode (uniswapDispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (uniswapX_short (g := Sat256.ofUInt256 g) hcode hwv hshort)
      |>.reEquivNoDispatch hcode (uniswapDispatch_none_short hshort)

/-- Reach a selected body in Uniswap's lowest selector group. -/
theorem uniswapReachLowestBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 5) (bodyPC : UInt256)
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) ≠ ⟨0⟩)
    (hlow :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapLowSplitPc) (uniswapSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapLowestFirstArmPc j))
        (uniswapSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapLowestFirstArmPc i))
        (uniswapSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J uniswapV2PairBytecode 0).contains bodyPC = true)
    (hbody :
      armTgt uniswapV2PairBytecode
        (nthArmPc uniswapV2PairBytecode uniswapLowestFirstArmPc i) = bodyPC) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h359⟩ :=
    uniswapReachLowestFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow
  exact RD.dispatchTo bodyPC i h359
    (fun j hj => uniswapLowestArmsWellFormed j (le_trans hj hi))
    heq0 htake
    (by rw [hbody]; exact hjd)
    hbody
    (by simp)

/-- Reach a selected body in Uniswap's middle-low selector group. -/
theorem uniswapReachMidLowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 2) (bodyPC : UInt256)
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) ≠ ⟨0⟩)
    (hlow :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapLowSplitPc) (uniswapSelWord I) = ⟨0⟩)
    (hmidLow :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapMidLowSplitPc) (uniswapSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapMidLowFirstArmPc j))
        (uniswapSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapMidLowFirstArmPc i))
        (uniswapSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J uniswapV2PairBytecode 0).contains bodyPC = true)
    (hbody :
      armTgt uniswapV2PairBytecode
        (nthArmPc uniswapV2PairBytecode uniswapMidLowFirstArmPc i) = bodyPC) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h321⟩ :=
    uniswapReachMidLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow hmidLow
  exact RD.dispatchTo bodyPC i h321
    (fun j hj => uniswapMidLowArmsWellFormed j (le_trans hj hi))
    heq0 htake
    (by rw [hbody]; exact hjd)
    hbody
    (by simp)

/-- Reach a selected body in Uniswap's low-upper selector group. -/
theorem uniswapReachLowUpperBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 3) (bodyPC : UInt256)
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) ≠ ⟨0⟩)
    (hlow :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapLowSplitPc) (uniswapSelWord I) = ⟨0⟩)
    (hmidLow :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapMidLowSplitPc) (uniswapSelWord I) =
        ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapLowUpperFirstArmPc j))
        (uniswapSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapLowUpperFirstArmPc i))
        (uniswapSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J uniswapV2PairBytecode 0).contains bodyPC = true)
    (hbody :
      armTgt uniswapV2PairBytecode
        (nthArmPc uniswapV2PairBytecode uniswapLowUpperFirstArmPc i) = bodyPC) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h272⟩ :=
    uniswapReachLowUpperFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow hmidLow
  exact RD.dispatchTo bodyPC i h272
    (fun j hj => uniswapLowUpperArmsWellFormed j (le_trans hj hi))
    heq0 htake
    (by rw [hbody]; exact hjd)
    hbody
    (by simp)

/-- Reach a selected body in Uniswap's high-upper selector group. -/
theorem uniswapReachHighUpperBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 3) (bodyPC : UInt256)
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) =
        ⟨0⟩)
    (hhigh :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapHighSplitPc) (uniswapSelWord I) =
        ⟨0⟩)
    (hhighMid :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapHighMidSplitPc) (uniswapSelWord I) =
        ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapHighUpperFirstArmPc j))
        (uniswapSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapHighUpperFirstArmPc i))
        (uniswapSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J uniswapV2PairBytecode 0).contains bodyPC = true)
    (hbody :
      armTgt uniswapV2PairBytecode
        (nthArmPc uniswapV2PairBytecode uniswapHighUpperFirstArmPc i) = bodyPC) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h65⟩ :=
    uniswapReachHighUpperFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh hhighMid
  exact RD.dispatchTo bodyPC i h65
    (fun j hj => uniswapHighUpperArmsWellFormed j (le_trans hj hi))
    heq0 htake
    (by rw [hbody]; exact hjd)
    hbody
    (by simp)

/-- Reach a selected body in Uniswap's high-middle selector group. -/
theorem uniswapReachHighMiddleBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 2) (bodyPC : UInt256)
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) =
        ⟨0⟩)
    (hhigh :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapHighSplitPc) (uniswapSelWord I) =
        ⟨0⟩)
    (hhighMid :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapHighMidSplitPc) (uniswapSelWord I) ≠
        ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapHighMiddleFirstArmPc j))
        (uniswapSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapHighMiddleFirstArmPc i))
        (uniswapSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J uniswapV2PairBytecode 0).contains bodyPC = true)
    (hbody :
      armTgt uniswapV2PairBytecode
        (nthArmPc uniswapV2PairBytecode uniswapHighMiddleFirstArmPc i) = bodyPC) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h114⟩ :=
    uniswapReachHighMiddleFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh hhighMid
  exact RD.dispatchTo bodyPC i h114
    (fun j hj => uniswapHighMiddleArmsWellFormed j (le_trans hj hi))
    heq0 htake
    (by rw [hbody]; exact hjd)
    hbody
    (by simp)

/-- Reach a selected body in Uniswap's high-lower selector group. -/
theorem uniswapReachHighLowerBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 3) (bodyPC : UInt256)
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) =
        ⟨0⟩)
    (hhigh :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapHighSplitPc) (uniswapSelWord I) ≠
        ⟨0⟩)
    (hlower :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapHighLowerSplitPc) (uniswapSelWord I) =
        ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapHighLowerFirstArmPc j))
        (uniswapSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapHighLowerFirstArmPc i))
        (uniswapSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J uniswapV2PairBytecode 0).contains bodyPC = true)
    (hbody :
      armTgt uniswapV2PairBytecode
        (nthArmPc uniswapV2PairBytecode uniswapHighLowerFirstArmPc i) = bodyPC) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h163⟩ :=
    uniswapReachHighLowerFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh hlower
  exact RD.dispatchTo bodyPC i h163
    (fun j hj => uniswapHighLowerArmsWellFormed j (le_trans hj hi))
    heq0 htake
    (by rw [hbody]; exact hjd)
    hbody
    (by simp)

/-- Reach a selected body in Uniswap's high-lowest selector group. -/
theorem uniswapReachHighLowestBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 2) (bodyPC : UInt256)
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) =
        ⟨0⟩)
    (hhigh :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapHighSplitPc) (uniswapSelWord I) ≠
        ⟨0⟩)
    (hlower :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapHighLowerSplitPc) (uniswapSelWord I) ≠
        ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapHighLowestFirstArmPc j))
        (uniswapSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapHighLowestFirstArmPc i))
        (uniswapSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J uniswapV2PairBytecode 0).contains bodyPC = true)
    (hbody :
      armTgt uniswapV2PairBytecode
        (nthArmPc uniswapV2PairBytecode uniswapHighLowestFirstArmPc i) = bodyPC) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h212⟩ :=
    uniswapReachHighLowestFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh hlower
  exact RD.dispatchTo bodyPC i h212
    (fun j hj => uniswapHighLowestArmsWellFormed j (le_trans hj hi))
    heq0 htake
    (by rw [hbody]; exact hjd)
    hbody
    (by simp)

/-- Reach the `PERMIT_TYPEHASH()` body entry through the optimized dispatcher. -/
theorem uniswapReachPermitTypehashBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x30, 0xad, 0xf8, 0x1f]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨933⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : uniswapSelWord I = ⟨0x30adf81f⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x30 0xad 0xf8 0x1f ⟨0x30adf81f⟩ (by decide) hsel
  exact uniswapReachMidLowBody 1 (by decide) ⟨933⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j
      all_goals decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `decimals()` body entry through the optimized dispatcher. -/
theorem uniswapReachDecimalsBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x31, 0x3c, 0xe5, 0x67]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨941⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : uniswapSelWord I = ⟨0x313ce567⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x31 0x3c 0xe5 0x67 ⟨0x313ce567⟩ (by decide) hsel
  exact uniswapReachMidLowBody 2 (by decide) ⟨941⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j
      all_goals native_decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `transferFrom(address,address,uint256)` body entry through the optimized dispatcher. -/
theorem uniswapReachTransferFromBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨879⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : uniswapSelWord I = ⟨0x23b872dd⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x23 0xb8 0x72 0xdd ⟨0x23b872dd⟩ (by decide) hsel
  exact uniswapReachMidLowBody 0 (by decide) ⟨879⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => False.elim ((Nat.not_lt_zero j) hj))
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `DOMAIN_SEPARATOR()` body entry through the optimized dispatcher. -/
theorem uniswapReachDomainSeparatorBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x36, 0x44, 0xe5, 0x15]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨971⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : uniswapSelWord I = ⟨0x3644e515⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x36 0x44 0xe5 0x15 ⟨0x3644e515⟩ (by decide) hsel
  exact uniswapReachLowUpperBody 0 (by decide) ⟨971⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => False.elim ((Nat.not_lt_zero j) hj))
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `initialize(address,address)` body entry through the optimized dispatcher. -/
theorem uniswapReachInitializeBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x48, 0x5c, 0xc9, 0x55]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨979⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : uniswapSelWord I = ⟨0x485cc955⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x48 0x5c 0xc9 0x55 ⟨0x485cc955⟩ (by decide) hsel
  exact uniswapReachLowUpperBody 1 (by decide) ⟨979⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j
      all_goals decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `price0CumulativeLast()` body entry through the optimized dispatcher. -/
theorem uniswapReachPrice0CumulativeLastBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x59, 0x09, 0xc0, 0xd5]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1025⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : uniswapSelWord I = ⟨0x5909c0d5⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x59 0x09 0xc0 0xd5 ⟨0x5909c0d5⟩ (by decide) hsel
  exact uniswapReachLowUpperBody 2 (by decide) ⟨1025⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j
      all_goals native_decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `price1CumulativeLast()` body entry through the optimized dispatcher. -/
theorem uniswapReachPrice1CumulativeLastBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x5a, 0x3d, 0x54, 0x93]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1033⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : uniswapSelWord I = ⟨0x5a3d5493⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x5a 0x3d 0x54 0x93 ⟨0x5a3d5493⟩ (by decide) hsel
  exact uniswapReachLowUpperBody 3 (by decide) ⟨1033⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j
      all_goals native_decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `balanceOf(address)` body entry through the optimized dispatcher. -/
theorem uniswapReachBalanceOfBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x70, 0xa0, 0x82, 0x31]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1079⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : uniswapSelWord I = ⟨0x70a08231⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x70 0xa0 0x82 0x31 ⟨0x70a08231⟩ (by decide) hsel
  exact uniswapReachHighLowestBody 1 (by decide) ⟨1079⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j
      all_goals decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `kLast()` body entry through the optimized dispatcher. -/
theorem uniswapReachKLastBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x74, 0x64, 0xfc, 0x3d]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1117⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : uniswapSelWord I = ⟨0x7464fc3d⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x74 0x64 0xfc 0x3d ⟨0x7464fc3d⟩ (by decide) hsel
  exact uniswapReachHighLowestBody 2 (by decide) ⟨1117⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j
      all_goals native_decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `nonces(address)` body entry through the optimized dispatcher. -/
theorem uniswapReachNoncesBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x7e, 0xce, 0xbe, 0x00]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1125⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : uniswapSelWord I = ⟨0x7ecebe00⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x7e 0xce 0xbe 0x00 ⟨0x7ecebe00⟩ (by decide) hsel
  exact uniswapReachHighLowerBody 0 (by decide) ⟨1125⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => False.elim ((Nat.not_lt_zero j) hj))
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `MINIMUM_LIQUIDITY()` body entry through the optimized dispatcher. -/
theorem uniswapReachMinimumLiquidityBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xba, 0x9a, 0x7a, 0x56]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1278⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : uniswapSelWord I = ⟨0xba9a7a56⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0xba 0x9a 0x7a 0x56 ⟨0xba9a7a56⟩ (by decide) hsel
  exact uniswapReachHighMiddleBody 0 (by decide) ⟨1278⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => False.elim ((Nat.not_lt_zero j) hj))
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `factory()` body entry through the optimized dispatcher. -/
theorem uniswapReachFactoryBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xc4, 0x5a, 0x01, 0x55]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1324⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : uniswapSelWord I = ⟨0xc45a0155⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0xc4 0x5a 0x01 0x55 ⟨0xc45a0155⟩ (by decide) hsel
  exact uniswapReachHighMiddleBody 2 (by decide) ⟨1324⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j
      all_goals native_decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `token1()` body entry through the optimized dispatcher. -/
theorem uniswapReachToken1Body {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xd2, 0x12, 0x20, 0xa7]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1332⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : uniswapSelWord I = ⟨0xd21220a7⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0xd2 0x12 0x20 0xa7 ⟨0xd21220a7⟩ (by decide) hsel
  exact uniswapReachHighUpperBody 0 (by decide) ⟨1332⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => False.elim ((Nat.not_lt_zero j) hj))
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `allowance(address,address)` body entry through the optimized dispatcher. -/
theorem uniswapReachAllowanceBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1421⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : uniswapSelWord I = ⟨0xdd62ed3e⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0xdd 0x62 0xed 0x3e ⟨0xdd62ed3e⟩ (by decide) hsel
  exact uniswapReachHighUpperBody 2 (by decide) ⟨1421⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j
      all_goals native_decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `sync()` body entry through the optimized dispatcher. -/
theorem uniswapReachSyncBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1467⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : uniswapSelWord I = ⟨0xfff6cae9⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0xff 0xf6 0xca 0xe9 ⟨0xfff6cae9⟩ (by decide) hsel
  exact uniswapReachHighUpperBody 3 (by decide) ⟨1467⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j
      all_goals native_decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `skim(address)` body entry through the optimized dispatcher. -/
theorem uniswapReachSkimBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1286⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : uniswapSelWord I = ⟨0xbc25cf77⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0xbc 0x25 0xcf 0x77 ⟨0xbc25cf77⟩ (by decide) hsel
  exact uniswapReachHighMiddleBody 1 (by decide) ⟨1286⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j
      all_goals decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `getReserves()` body entry through the optimized dispatcher. -/
theorem uniswapReachGetReservesBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x09, 0x02, 0xf1, 0xac]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨697⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : uniswapSelWord I = ⟨0x0902f1ac⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x09 0x02 0xf1 0xac ⟨0x0902f1ac⟩ (by decide) hsel
  exact uniswapReachLowestBody 2 (by decide) ⟨697⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j <;> decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `token0()` body entry through the optimized dispatcher. -/
theorem uniswapReachToken0Body {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x0d, 0xfe, 0x16, 0x81]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨817⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : uniswapSelWord I = ⟨0x0dfe1681⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x0d 0xfe 0x16 0x81 ⟨0x0dfe1681⟩ (by decide) hsel
  exact uniswapReachLowestBody 4 (by decide) ⟨817⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j <;> decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `approve(address,uint256)` body entry through the optimized dispatcher. -/
theorem uniswapReachApproveBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨753⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : uniswapSelWord I = ⟨0x095ea7b3⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x09 0x5e 0xa7 0xb3 ⟨0x095ea7b3⟩ (by decide) hsel
  exact uniswapReachLowestBody 3 (by decide) ⟨753⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j
      all_goals native_decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `totalSupply()` body entry through the optimized dispatcher. -/
theorem uniswapReachTotalSupplyBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨853⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : uniswapSelWord I = ⟨0x18160ddd⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x18 0x16 0x0d 0xdd ⟨0x18160ddd⟩ (by decide) hsel
  have hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide
  have hlow :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapLowSplitPc) (uniswapSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide
  exact uniswapReachLowestBody 5 (by decide) ⟨853⟩ hcode hwv hsz hsize hroot hlow
    (fun j hj => by
      rw [hword]
      interval_cases j <;> decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `transfer(address,uint256)` body entry through the optimized dispatcher. -/
theorem uniswapReachTransferBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1234⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : uniswapSelWord I = ⟨0xa9059cbb⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0xa9 0x05 0x9c 0xbb ⟨0xa9059cbb⟩ (by decide) hsel
  exact uniswapReachHighLowerBody 3 (by decide) ⟨1234⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j
      all_goals native_decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

end UniswapV2Pair
