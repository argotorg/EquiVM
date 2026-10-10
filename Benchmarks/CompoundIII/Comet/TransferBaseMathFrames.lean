import Benchmarks.CompoundIII.Comet.TransferBaseMathModel
import Benchmarks.CompoundIII.Comet.BaseBalanceSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def transferBaseBalanceBlock : List Stmt :=
  baseBalanceBlock true "srcPrincipal" "__c1" "__c2" "srcBalance" ++
    baseBalanceBlock false "dstPrincipal" "__c3" "__c4" "dstBalance"

def transferBaseSrcBalanceFrame (frame : Frame) (evm : EVM.State)
    (srcPrincipal amount : UInt256) : Frame :=
  { frame with
    locals := ((frame.locals.insert "__c1" (.int (signedPresentValueInt evm srcPrincipal))).insert
      "__c2" (.int amount.toNat)).insert "srcBalance"
        (.int (withdrawBaseBalanceInt evm srcPrincipal amount)) }

def transferBaseBalanceFrame (frame : Frame) (evm : EVM.State)
    (srcPrincipal dstPrincipal amount : UInt256) : Frame :=
  let f := transferBaseSrcBalanceFrame frame evm srcPrincipal amount
  { f with
    locals := ((f.locals.insert "__c3" (.int (signedPresentValueInt evm dstPrincipal))).insert
      "__c4" (.int amount.toNat)).insert "dstBalance"
        (.int (supplyBaseBalanceInt evm dstPrincipal amount)) }

def transferBasePrincipalBlock : List Stmt :=
  [.internalCall "principalValue" [.var "srcBalance"] "srcPrincipalNew",
    .internalCall "principalValue" [.var "dstBalance"] "dstPrincipalNew"]

def transferBasePrincipalFrame (frame : Frame) (evm : EVM.State)
    (srcPrincipal dstPrincipal amount : UInt256) : Frame :=
  { frame with
    locals := (frame.locals.insert "srcPrincipalNew"
      (.int (principalValueInt evm (withdrawBaseBalance evm srcPrincipal amount)))).insert
      "dstPrincipalNew" (.int (principalValueInt evm (supplyBaseBalance evm dstPrincipal amount))) }

def transferBaseAmountsBlock : List Stmt :=
  [.internalCall "withdrawAndBorrowAmount" [.var "srcPrincipal", .var "srcPrincipalNew"] "__c7",
    .letDecl "withdrawAmount" (some (.elem (.int (.uint ⟨104, by decide⟩))))
      (.tupleGet (.var "__c7") 0),
    .letDecl "borrowAmount" (some (.elem (.int (.uint ⟨104, by decide⟩))))
      (.tupleGet (.var "__c7") 1),
    .internalCall "repayAndSupplyAmount" [.var "dstPrincipal", .var "dstPrincipalNew"] "__c8",
    .letDecl "repayAmount" (some (.elem (.int (.uint ⟨104, by decide⟩))))
      (.tupleGet (.var "__c8") 0),
    .letDecl "supplyAmount" (some (.elem (.int (.uint ⟨104, by decide⟩))))
      (.tupleGet (.var "__c8") 1)]

def transferBaseAmountsFrame (frame : Frame) (srcPrincipal dstPrincipal srcNext dstNext : UInt256) :
    Frame :=
  let withdrawn := withdrawSupplyAmount srcPrincipal srcNext
  let borrowed := withdrawBorrowAmount srcPrincipal srcNext
  let repaid := repayAmount dstPrincipal dstNext
  let supplied := supplyAmount dstPrincipal dstNext
  { frame with
    locals := (((((frame.locals.insert "__c7" (.tuple [.int withdrawn.toNat, .int borrowed.toNat])
      ).insert "withdrawAmount" (.int withdrawn.toNat)).insert "borrowAmount" (.int borrowed.toNat)
      ).insert "__c8" (.tuple [.int repaid.toNat, .int supplied.toNat])).insert "repayAmount"
      (.int repaid.toNat)).insert "supplyAmount" (.int supplied.toNat) }

def transferBaseMathBlock : List Stmt :=
  transferBaseBalanceBlock ++ transferBasePrincipalBlock ++ transferBaseAmountsBlock

def transferBaseMathFrame (frame : Frame) (evm : EVM.State)
    (srcPrincipal dstPrincipal amount : UInt256) : Frame :=
  transferBaseAmountsFrame
    (transferBasePrincipalFrame
      (transferBaseBalanceFrame frame evm srcPrincipal dstPrincipal amount)
      evm srcPrincipal dstPrincipal amount)
    srcPrincipal dstPrincipal (withdrawBasePrincipal evm srcPrincipal amount)
      (supplyBasePrincipal evm dstPrincipal amount)

end Benchmarks.CompoundIII.Comet
