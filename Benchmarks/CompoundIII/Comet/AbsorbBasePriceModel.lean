import Benchmarks.CompoundIII.Comet.AbsorbLoopTailModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

inductive AbsorbBasePriceTrace (v : CometWithExtendedAssetListImmutables) (account : AccountAddress)
    (basic : UserBasicData) (old : UInt256) (evm : State) : InternalOutcome → Prop where
  | priceFailed {evm' z out}
      (hc : callViaEVM evm v.baseTokenPriceFeed 0 pricePayload (z, evm', out) false)
      (hh : out.size < 2^255) (hv : ¬ (z = true ∧ PriceValid out)) :
      AbsorbBasePriceTrace v account basic old evm .reverted
  | finished {evm' out result}
      (hc : callViaEVM evm v.baseTokenPriceFeed 0 pricePayload (true, evm', out) false)
      (hh : out.size < 2^255) (hv : PriceValid out)
      (ht : AbsorbLoopTailTrace v account basic old (calldataWord out 32) 0 ⟨0⟩ evm' result) :
      AbsorbBasePriceTrace v account basic old evm result

def absorbBasePriceFrame (frame : Frame) (price : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "basePrice" (.int price.toNat) }

def absorbInitialFrame (frame : Frame) (price : UInt256) : Frame :=
  let f := absorbBasePriceFrame frame price
  { f with locals := (f.locals.insert "deltaValue" (.int 0)).insert "i" (.int 0) }

def absorbBasePriceBlock : List Stmt :=
  .internalCall "getPrice_body" [.immutable "baseTokenPriceFeed"] "basePrice" ::
    .letDecl "deltaValue" (some (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit 0) ::
    .letDecl "i" (some (.elem (.int (.uint ⟨8, by decide⟩)))) (.intLit 0) ::
    absorbLoopTailBlock

end Benchmarks.CompoundIII.Comet
