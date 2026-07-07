import Benchmarks.Dss.Cat.BiteConnect
import Benchmarks.Dss.Cat.BiteRevertPrim
import Benchmarks.Dss.Cat.BiteSource
import Benchmarks.Dss.Cat.BiteTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.Dss.Cat

/-! # Cat `bite(bytes32,address)` — revert leaves

Each leaf concludes the SUCCESS-branch `runtimeEquivalenceFor …` shape but under a failing-condition
hypothesis, via the revert path: reach the divergence with the public `catBiteReach*`/`catBiteTraceSeg*`
segment lemmas, fire the matching revert primitive to get `RDrev`, and bridge to the Solm body's
`.reverted` result with `RDrev.reEquivExecutionRevert` + the matching `catBiteSource*Revert`.

Template: `catBiteShort` (BiteConnect.lean). Revert primitives: `RD.catBiteCheckedMulRevert`,
`RD.solcErrorStringRevertTailGrown`, `RD.solcCheckedSubStringRevertGrown`,
`RD.reachInvalidHalt`, and `RD.catBite{Grab,Fess,Kick}CallFailed`.

**Reach-cursor convention.** The entry→divergence reach assembler `catBiteBody` (Bite.lean) is not
yet completed (the inter-call return-data→memory threading is still open). Exactly as the success
leaf `catBiteSuccessLeaf` takes the whole-run `RDret` as a hypothesis, each revert leaf takes the EVM
reach cursor *at the divergence* as a hypothesis and completes the revert branch: fire the primitive
→ `RDrev`, run the Solm `catBiteSource*Revert`, bridge with `RDrev.reEquivExecutionRevert`. When the
reach assembler lands, its cursors discharge these hypotheses. -/

/-- **mul-overflow leaf (artRate = art·rate).** EVM cursor at the shared `checkedMul` routine `@3720`
with the `artRate` operands; overflow (`hover`) fires `RD.catBiteCheckedMulRevert`, the Solm body
reverts via `catBiteSourceArtRateOverflowRevert`, bridged by `RDrev.reEquivExecutionRevert`. -/
theorem catBiteArtRateOverflowLeaf {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {evmIlk evmUrn : EVM.State} {ilksOut urnsOut : ByteArray}
    {iArt iRate iSpot iLine iDust ink art ret : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {R : List UInt256} {k C : ℕ}
    (hcode : I.code = catBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3720⟩
      (iRate :: art :: ret :: R) mem aw rdata acc k C)
    (hov : R.length + 9 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩)
    (hvatCode0 :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (biteVatAddr (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).option 0
          (fun acc => acc.code.size))).toNat)
    (hIlksCall :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (biteVatAddr (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
        "ilks" 0 [biteIlkVal I] (true, evmIlk, ilksOut) false)
    (hIlksDec :
      config.externalABI.decode? "ilks" ilksOut =
        some [bw iArt, bw iRate, bw iSpot, bw iLine, bw iDust])
    (hvatCodeIlk :
      0 < (UInt256.ofNat
        ((evmIlk.lookupAccount (biteVatAddr evmIlk)).option 0 (fun acc => acc.code.size))).toNat)
    (hUrnsCall :
      typedCallViaEVM config evmIlk (EVM.address (biteVatAddr evmIlk))
        "urns" 0 [biteIlkVal I, biteUrnVal I] (true, evmUrn, urnsOut) false)
    (hUrnsDec : config.externalABI.decode? "urns" urnsOut = some [bw ink, bw art])
    (hlive : catSlotWord ⟨2⟩ evmUrn.accountMap evmUrn.executionEnv = ⟨1⟩)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size) (hspotPos : 0 < iSpot.toNat)
    (hover : UInt256.size ≤ art.toNat * iRate.toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev : RDrev catBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    RD.catBiteCheckedMulRevert rd (by rw [Nat.mul_comm]; exact hover) hov
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
        biteTransition.body .reverted :=
    catBiteSourceArtRateOverflowRevert hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk
      hUrnsCall hUrnsDec hlive hfitInkSpot hspotPos hover
  have hfinal := hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  simpa using hfinal

/-- **call-fail leaf (kick).** EVM cursor at the `kick` success-guard `@2532` with a failed-call
status `⟨0⟩` on top; `RD.catBiteKickCallFailed` produces `RDrev`, bridged by
`RDrev.reEquivExecutionRevert`. The Solm body reverts via `catBiteSourceKickFailRevert` (green in
BiteSource; its `ExecTransitionBody … .reverted` is taken here as `hbody`, plugging in identically to
the mul-overflow leaf's `catBiteSourceArtRateOverflowRevert`). -/
theorem catBiteKickFailLeaf {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {R : List UInt256} {k C : ℕ}
    (hcode : I.code = catBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2532⟩
      (⟨0⟩ :: R) mem aw rdata acc k C)
    (hrdataSize : rdata.size < UInt256.size) (hov : R.length + 5 ≤ 1024)
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
        biteTransition.body .reverted) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev : RDrev catBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    RD.catBiteKickCallFailed rd hrdataSize hov
  simpa using hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

end Benchmarks.Dss.Cat
