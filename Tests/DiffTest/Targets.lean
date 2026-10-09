import Solm.DiffTest.Harness
import Examples.ERC20.Spec
import Examples.ERC20.Bytecode
import Examples.Ballot.Spec
import Examples.Ballot.Bytecode
import Examples.SimpleAuction.Spec
import Examples.SimpleAuction.Bytecode
import Examples.BlindAuction.Spec
import Examples.BlindAuction.Bytecode
import Examples.Caller.Spec
import Examples.Caller.Bytecode
import Examples.Pow.Spec
import Examples.Pow.Bytecode
import Examples.Truth.Spec
import Examples.Truth.Bytecode
import Examples.StringStoreLite.Spec
import Examples.StringStoreLite.Bytecode
import Examples.Reuse.Spec
import Examples.Reuse.Bytecode
import Benchmarks.WETH9.Spec
import Benchmarks.WETH9.Bytecode
import Benchmarks.Dss.Pot.Spec
import Benchmarks.Dss.Pot.Bytecode
import Examples.TinyImmutable.Spec
import Examples.TinyImmutable.Bytecode
import Examples.TinyImmutable.ImmutableCode
import Tests.DiffTest.Generated
import Benchmarks.Auction.Spec
import Benchmarks.Auction.Bytecode
import Benchmarks.Dss.Cat.Spec
import Benchmarks.Dss.Cat.Bytecode
import Benchmarks.Dss.Cure.Spec
import Benchmarks.Dss.Cure.Bytecode
import Benchmarks.Dss.Dai.Spec
import Benchmarks.Dss.Dai.Bytecode
import Benchmarks.Dss.DaiJoin.Spec
import Benchmarks.Dss.DaiJoin.Bytecode
import Benchmarks.Dss.End.Spec
import Benchmarks.Dss.End.Bytecode
import Benchmarks.Dss.ExponentialDecrease.Spec
import Benchmarks.Dss.ExponentialDecrease.Bytecode
import Benchmarks.Dss.Flapper.Spec
import Benchmarks.Dss.Flapper.Bytecode
import Benchmarks.Dss.Flipper.Spec
import Benchmarks.Dss.Flipper.Bytecode
import Benchmarks.Dss.Flopper.Spec
import Benchmarks.Dss.Flopper.Bytecode
import Benchmarks.Dss.GemJoin.Spec
import Benchmarks.Dss.GemJoin.Bytecode
import Benchmarks.Dss.Jug.Spec
import Benchmarks.Dss.Jug.Bytecode
import Benchmarks.Dss.LinearDecrease.Spec
import Benchmarks.Dss.LinearDecrease.Bytecode
import Benchmarks.Dss.Spot.Spec
import Benchmarks.Dss.Spot.Bytecode
import Benchmarks.Dss.StairstepExponentialDecrease.Spec
import Benchmarks.Dss.StairstepExponentialDecrease.Bytecode
import Benchmarks.Dss.Vat.Spec
import Benchmarks.Dss.Vat.Bytecode
import Benchmarks.Dss.Vow.Spec
import Benchmarks.Dss.Vow.Bytecode
import Examples.UniswapV2Pair.Spec
import Examples.UniswapV2Pair.Bytecode
import Examples.VyperERC20.Spec
import Examples.VyperERC20.Bytecode
import Examples.CtorStore.Spec
import Examples.CtorStore.Bytecode
import Examples.CtorTruth.Spec
import Examples.CtorTruth.Bytecode
import Benchmarks.Scaffolds.ERC721.Spec
import Benchmarks.Scaffolds.ERC721.Bytecode
import Benchmarks.Scaffolds.Klima.Spec
import Benchmarks.Scaffolds.Klima.Bytecode
import Benchmarks.Scaffolds.Safe.Spec
import Benchmarks.Scaffolds.Safe.Bytecode
import Benchmarks.Scaffolds.TimelockController.Spec
import Benchmarks.Scaffolds.TimelockController.Bytecode
import Benchmarks.Scaffolds.VestingWallet.Spec
import Benchmarks.Scaffolds.VestingWallet.Bytecode

/-!
# Differential test targets

Every registered specification with its compiled artifact.  Add a target here to put a contract
under the differential suite; `Main.lean` runs them all.
-/

namespace Tests.DiffTest

open Solm Solm.DiffTest Ethereum

def erc20 : Target :=
  { name := "ERC20", contract := ERC20.erc20Contract, config := erc20Config,
    runtime := erc20Bytecode, initcode := some erc20Initcode,
    callees := standardCallees, words := [10 ^ 18, 10 ^ 6] }

def ballot : Target :=
  { name := "Ballot", contract := Ballot.ballotContract, config := ballotConfig,
    runtime := ballotBytecode, callees := standardCallees, words := [0, 1, 2, 3, 7] }

def simpleAuction : Target :=
  { name := "SimpleAuction", contract := SimpleAuction.simpleAuctionContract,
    config := simpleAuctionConfig, runtime := simpleAuctionBytecode,
    initcode := some simpleAuctionInitcode, callees := standardCallees,
    words := [0, 1, 60, 3600, 10 ^ 18] }

def blindAuction : Target :=
  { name := "BlindAuction", contract := BlindAuction.blindAuctionContract,
    config := blindAuctionConfig, runtime := blindAuctionBytecode,
    initcode := some blindAuctionInitcode, callees := standardCallees,
    words := [0, 1, 60, 3600, 10 ^ 18] }

/-- `Caller.run(t, n)` calls `pow2(n)` on `t`: the callee pool includes a real `Pow` deployment. -/
def caller : Target :=
  { name := "Caller", contract := Caller.callerContract, config := callerConfig,
    runtime := callerBytecode, initcode := some callerInitcode,
    callees := (EVM.address 0x5100, powBytecode) :: standardCallees, words := [0, 1, 2, 7, 255, 256] }

def pow : Target :=
  { name := "Pow", contract := Pow.powContract, config := powConfig,
    runtime := powBytecode, initcode := some powInitcode, words := [0, 1, 2, 7, 255, 256, 257] }

def truth : Target :=
  { name := "Truth", contract := truthContract, config := truthConfig, runtime := truthBytecode }

def stringStoreLite : Target :=
  { name := "StringStoreLite", contract := StringStoreLite.stringStoreLiteContract,
    config := stringStoreLiteConfig, runtime := stringStoreLiteBytecode,
    initcode := some stringStoreLiteInitcode }

def reuse : Target :=
  { name := "Reuse", contract := Reuse.cContract, config := cConfig,
    runtime := cBytecode, initcode := some cInitcode }

def weth9 : Target :=
  { name := "WETH9", contract := Benchmarks.WETH9.contract, config := Benchmarks.WETH9.config,
    runtime := Benchmarks.WETH9.weth9Bytecode, initcode := some Benchmarks.WETH9.weth9CreationBytecode,
    callees := standardCallees, words := [10 ^ 18, 10 ^ 20, 2 ^ 256 - 1] }

def pot : Target :=
  { name := "Pot", contract := Benchmarks.Dss.Pot.contract, config := Benchmarks.Dss.Pot.config,
    runtime := Benchmarks.Dss.Pot.potBytecode, initcode := some Benchmarks.Dss.Pot.potCreationBytecode,
    callees := standardCallees, words := [10 ^ 27, 10 ^ 18, 10 ^ 45, 2 ^ 256 - 1] }

/-- TinyImmutable at one valuation: the runtime is the template patched with the immutables, and a
    constructor must return the template patched with its final immutables. -/
def tinyImmutable : Target :=
  let store : Store := ((∅ : Store).insert "owner" (.address (EVM.address 0x2000))).insert "scale" (.int 3)
  { name := "TinyImmutable", contract := TinyImmutable.contract, config := TinyImmutable.config,
    runtime := TinyImmutable.immutableLayout.deployed TinyImmutable.tinyImmutableBytecode store,
    immutables := store, initcode := some TinyImmutable.tinyImmutableCreationBytecode,
    runtimeCodeOf := some fun imms => TinyImmutable.immutableLayout.deployed TinyImmutable.tinyImmutableBytecode imms,
    words := [0, 1, 3, 2 ^ 128, 2 ^ 256 - 1] }

/-! ## Benchmarks -/

/-- Dss constants: RAY, WAD, RAD. -/
def dssWords : List Nat := [10 ^ 27, 10 ^ 18, 10 ^ 45, 2 ^ 256 - 1]

def dss (name : String) (contract : ContractDecl) (config : Config) (runtime initcode : ByteArray) : Target :=
  { name, contract, config, runtime, initcode := some initcode, callees := standardCallees, words := dssWords }

def cat : Target :=
  dss "Cat" Benchmarks.Dss.Cat.contract Benchmarks.Dss.Cat.config Benchmarks.Dss.Cat.catBytecode
    Benchmarks.Dss.Cat.catCreationBytecode

def cure : Target :=
  dss "Cure" Benchmarks.Dss.Cure.contract Benchmarks.Dss.Cure.config Benchmarks.Dss.Cure.cureBytecode
    Benchmarks.Dss.Cure.cureCreationBytecode

def dai : Target :=
  dss "Dai" Benchmarks.Dss.Dai.contract Benchmarks.Dss.Dai.config Benchmarks.Dss.Dai.daiBytecode
    Benchmarks.Dss.Dai.daiCreationBytecode

def daiJoin : Target :=
  dss "DaiJoin" Benchmarks.Dss.DaiJoin.contract Benchmarks.Dss.DaiJoin.config Benchmarks.Dss.DaiJoin.daiJoinBytecode
    Benchmarks.Dss.DaiJoin.daiJoinCreationBytecode

def dssEnd : Target :=
  dss "End" Benchmarks.Dss.End.contract Benchmarks.Dss.End.config Benchmarks.Dss.End.endBytecode
    Benchmarks.Dss.End.endCreationBytecode

def exponentialDecrease : Target :=
  dss "ExponentialDecrease" Benchmarks.Dss.ExponentialDecrease.contract Benchmarks.Dss.ExponentialDecrease.config Benchmarks.Dss.ExponentialDecrease.exponentialDecreaseBytecode
    Benchmarks.Dss.ExponentialDecrease.exponentialDecreaseCreationBytecode

def flapper : Target :=
  dss "Flapper" Benchmarks.Dss.Flapper.contract Benchmarks.Dss.Flapper.config Benchmarks.Dss.Flapper.flapperBytecode
    Benchmarks.Dss.Flapper.flapperCreationBytecode

def flipper : Target :=
  dss "Flipper" Benchmarks.Dss.Flipper.contract Benchmarks.Dss.Flipper.config Benchmarks.Dss.Flipper.flipperBytecode
    Benchmarks.Dss.Flipper.flipperCreationBytecode

def flopper : Target :=
  dss "Flopper" Benchmarks.Dss.Flopper.contract Benchmarks.Dss.Flopper.config Benchmarks.Dss.Flopper.flopperBytecode
    Benchmarks.Dss.Flopper.flopperCreationBytecode

def gemJoin : Target :=
  dss "GemJoin" Benchmarks.Dss.GemJoin.contract Benchmarks.Dss.GemJoin.config Benchmarks.Dss.GemJoin.gemJoinBytecode
    Benchmarks.Dss.GemJoin.gemJoinCreationBytecode

def jug : Target :=
  dss "Jug" Benchmarks.Dss.Jug.contract Benchmarks.Dss.Jug.config Benchmarks.Dss.Jug.jugBytecode
    Benchmarks.Dss.Jug.jugCreationBytecode

def linearDecrease : Target :=
  dss "LinearDecrease" Benchmarks.Dss.LinearDecrease.contract Benchmarks.Dss.LinearDecrease.config Benchmarks.Dss.LinearDecrease.linearDecreaseBytecode
    Benchmarks.Dss.LinearDecrease.linearDecreaseCreationBytecode

def spot : Target :=
  dss "Spot" Benchmarks.Dss.Spot.contract Benchmarks.Dss.Spot.config Benchmarks.Dss.Spot.spotBytecode
    Benchmarks.Dss.Spot.spotCreationBytecode

def stairstepExponentialDecrease : Target :=
  dss "StairstepExponentialDecrease" Benchmarks.Dss.StairstepExponentialDecrease.contract Benchmarks.Dss.StairstepExponentialDecrease.config Benchmarks.Dss.StairstepExponentialDecrease.stairstepExponentialDecreaseBytecode
    Benchmarks.Dss.StairstepExponentialDecrease.stairstepExponentialDecreaseCreationBytecode

def vat : Target :=
  dss "Vat" Benchmarks.Dss.Vat.contract Benchmarks.Dss.Vat.config Benchmarks.Dss.Vat.vatBytecode
    Benchmarks.Dss.Vat.vatCreationBytecode

def vow : Target :=
  dss "Vow" Benchmarks.Dss.Vow.contract Benchmarks.Dss.Vow.config Benchmarks.Dss.Vow.vowBytecode
    Benchmarks.Dss.Vow.vowCreationBytecode

def auction : Target :=
  { name := "Auction", contract := Auction.auctionContract, config := auctionConfig,
    runtime := auctionBytecode, initcode := some auctionCreationBytecode,
    callees := standardCallees, words := [0, 1, 60, 3600, 10 ^ 17, 10 ^ 18] }

def uniswapV2Pair : Target :=
  { name := "UniswapV2Pair", contract := UniswapV2Pair.contract, config := UniswapV2Pair.config,
    runtime := UniswapV2Pair.uniswapV2PairBytecode, callees := standardCallees,
    words := [10 ^ 3, 10 ^ 18, 2 ^ 112 - 1] }

/-- The ERC20 specification against Vyper's compiler output. -/
def vyperERC20 : Target :=
  { name := "VyperERC20", contract := ERC20.erc20Contract, config := vyperERC20Config,
    runtime := vyperERC20Bytecode, initcode := some vyperERC20Initcode,
    words := [10 ^ 18, 10 ^ 6] }

def ctorStore : Target :=
  { name := "CtorStore", contract := CtorStore.contract, config := ctorStoreConfig,
    runtime := ctorStoreRuntimeBytecode, initcode := some ctorStoreInitcode }

def ctorTruth : Target :=
  { name := "CtorTruth", contract := CtorTruth.contract, config := ctorTruthConfig,
    runtime := ctorTruthRuntimeBytecode, initcode := some ctorTruthInitcode }

/-! ## Scaffolds (specifications not yet proved) -/

def erc721 : Target :=
  { name := "ERC721", contract := ERC721.erc721Contract, config := erc721Config,
    runtime := erc721Bytecode, initcode := some erc721CreationBytecode,
    callees := standardCallees, words := [0, 1, 2, 3, 42] }

def klima : Target :=
  { name := "Klima", contract := Benchmarks.Klima.contract, config := Benchmarks.Klima.config,
    runtime := Benchmarks.Klima.klimaBytecode, initcode := some Benchmarks.Klima.klimaCreationBytecode,
    callees := standardCallees, words := [10 ^ 9, 10 ^ 18] }

/-- The owner and module linked lists walk random storage, which cycles until the gas or the fuel
    runs out: smaller budgets keep those (inconclusive) cases cheap. -/
def safe : Target :=
  { name := "Safe", contract := Benchmarks.Safe.contract, config := Benchmarks.Safe.config,
    runtime := Benchmarks.Safe.safeBytecode, initcode := some Benchmarks.Safe.safeCreationBytecode,
    callees := standardCallees, words := [0, 1, 2, 3], gas := 400000, fuel := 5000 }

def timelockController : Target :=
  { name := "TimelockController", contract := OpenZeppelinBench.TimelockController.contract,
    config := OpenZeppelinBench.TimelockController.config,
    runtime := OpenZeppelinBench.TimelockController.timelockControllerBenchBytecode,
    initcode := some OpenZeppelinBench.TimelockController.timelockControllerBenchCreationBytecode,
    callees := standardCallees, words := [0, 1, 60, 3600, 86400] }

/-- `vestingWalletBenchBytecode` is the unpatched template (zero words at the four immutable
    sites, although its docstring says otherwise); the constructor fixes `start = 0` and
    `duration = 365 days`, so the runtime is taken from a constructor run. -/
def vestingWallet : Target :=
  { name := "VestingWallet", contract := OpenZeppelinBench.VestingWallet.contract,
    config := OpenZeppelinBench.VestingWallet.config,
    runtime := OpenZeppelinBench.VestingWallet.vestingWalletBenchBytecode,
    initcode := some OpenZeppelinBench.VestingWallet.vestingWalletBenchCreationBytecode,
    deployedRuntime := true, callees := standardCallees, words := [0, 1, 60, 3600, 365 * 86400, 10 ^ 18] }

/-! ## Fixtures (contracts written for the suite) -/

/-- `Factory`: `new` with and without salt, `for`/`break`/`continue`, `try`/`catch`, `pop`, `delete`.
    The generated target, with a deployed `Child` in the callee pool so `tryGet` can succeed. -/
def factory : Target :=
  { Fixtures.Factory.diffTarget with
    callees := (EVM.address 0x5200, Fixtures.Factory.childRuntimeBytecode) :: standardCallees,
    words := [0, 1, 2, 3, 4, 5, 7] }

def fixtures : List Target := [factory]

def examples : List Target :=
  [truth, pow, reuse, erc20, caller, stringStoreLite, tinyImmutable, ballot, simpleAuction, blindAuction,
   ctorStore, ctorTruth, vyperERC20, uniswapV2Pair]

def benchmarks : List Target :=
  [weth9, auction, pot, cat, cure, dai, daiJoin, dssEnd, exponentialDecrease, flapper, flipper, flopper, gemJoin, jug, linearDecrease, spot, stairstepExponentialDecrease, vat, vow]

def scaffolds : List Target :=
  [erc721, klima, safe, timelockController, vestingWallet]

/-- Every target: the ones above, then the generated ones (`Generated.lean`) not already named. -/
def allTargets : List Target :=
  let manual := fixtures ++ examples ++ benchmarks ++ scaffolds
  manual ++ generatedTargets.filter fun t => !manual.any (·.name == t.name)

end Tests.DiffTest
