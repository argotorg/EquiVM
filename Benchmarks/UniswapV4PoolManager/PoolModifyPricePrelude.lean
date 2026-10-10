import Benchmarks.UniswapV4PoolManager.PoolModifyContext
import Benchmarks.UniswapV4PoolManager.PoolFeeInsidePrelude
import Benchmarks.UniswapV4PoolManager.Slot0Source
import Benchmarks.UniswapV4PoolManager.PoolCheckSource
import Benchmarks.UniswapV4PoolManager.WordLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolSqrtPrice_bound (evm : State) (id : UInt256) : (poolSqrtPriceWord evm id).toNat < 2^160 :=
  u256LandMaskToNatLtOfToNat _ _ rfl
def poolModifyPricePreludeBlock : List Stmt :=
  [.letDecl "_slot0" (some abiBytes32) (.storage {base := "self", steps := [.field "slot0"]}),
   .internalCall "Slot0Library_tick" [.var "_slot0"] "__c14",
   .letDecl "tick" (some (.elem (.int (.sint ⟨24, by decide⟩)))) (.var "__c14"),
   .internalCall "Slot0Library_sqrtPriceX96" [.var "_slot0"] "__c15",
   .letDecl "sqrtPriceX96" (some (.elem (.int (.uint ⟨160, by decide⟩)))) (.var "__c15")]
def poolModifyPricePreludeFrame (f : Frame) (evm : State) (id : UInt256) : Frame :=
  let f0 := {f with locals := f.locals.insert "_slot0" (wordBytes32Value (poolSlot0Word evm id))}
  let f1 := {f0 with locals := f0.locals.insert "__c14" (.int (poolCurrentTick evm id))}
  let f2 := {f1 with locals := f1.locals.insert "tick" (.int (poolCurrentTick evm id))}
  wordLocal (wordLocal f2 "__c15" (poolSqrtPriceWord evm id)) "sqrtPriceX96" (poolSqrtPriceWord evm id)

theorem poolModifyPricePrelude {f : Frame} {evm : State} {id : UInt256} {p : PoolModifyParams}
    (hc : PoolModifyContext f id p) :
    ExecBlock config f evm poolModifyPricePreludeBlock (.ok (poolModifyPricePreludeFrame f evm id) evm) := by
  let f0 := {f with locals := f.locals.insert "_slot0" (wordBytes32Value (poolSlot0Word evm id))}
  let f1 := {f0 with locals := f0.locals.insert "__c14" (.int (poolCurrentTick evm id))}
  let f2 := {f1 with locals := f1.locals.insert "tick" (.int (poolCurrentTick evm id))}
  let f3 := wordLocal f2 "__c15" (poolSqrtPriceWord evm id)
  have h0 : ExecStmt config f evm poolModifyPricePreludeBlock[0]! (.ok f0 evm) :=
    ExecStmt.letDecl (poolSlot0_read hc.self)
  have h1 := slot0TickCall (f := f0) (evm := evm) hc.contract (evalLocalValue (store_get_self _ _ _)) "__c14"
  have h2 : ExecStmt config f1 evm poolModifyPricePreludeBlock[2]! (.ok f2 evm) :=
    ExecStmt.letDecl (evalLocalValue (store_get_self _ _ _))
  have hslot : f2.locals.get? "_slot0" = some (wordBytes32Value (poolSlot0Word evm id)) :=
    (store_get_ne2 _ _ _ (by decide : ("__c14" == "_slot0") = false)
      (by decide : ("tick" == "_slot0") = false)).trans (store_get_self _ _ _)
  have h3 := slot0SqrtCall (f := f2) (evm := evm) hc.contract (evalLocalValue hslot) "__c15"
  have h4 : ExecStmt config f3 evm poolModifyPricePreludeBlock[4]! (.ok (poolModifyPricePreludeFrame f evm id) evm) :=
    ExecStmt.letDecl (evalLocalValue (store_get_self _ _ _))
  exact ExecBlock.consNormal h0 (ExecBlock.consNormal h1 (ExecBlock.consNormal h2
    (ExecBlock.consNormal h3 (execBlock_singleton h4))))

theorem poolModifyPricePreludeFrame_context {f : Frame} {id : UInt256} {p : PoolModifyParams}
    (hc : PoolModifyContext f id p) (evm : State) :
    PoolModifyContext (poolModifyPricePreludeFrame f evm id) id p :=
  ((((hc.insert "_slot0" _ (by decide)).insert "__c14" _ (by decide)).insert "tick" _ (by decide)).insert
    "__c15" _ (by decide)).insert "sqrtPriceX96" _ (by decide)

theorem poolModifyPricePreludeFrame_get (f : Frame) (evm : State) (id : UInt256) (name : Ident)
    (hs : ("_slot0" == name) = false) (h14 : ("__c14" == name) = false) (ht : ("tick" == name) = false)
    (h15 : ("__c15" == name) = false) (hp : ("sqrtPriceX96" == name) = false) :
    (poolModifyPricePreludeFrame f evm id).locals.get? name = f.locals.get? name :=
  store_get_ne5 _ _ _ _ _ _ hs h14 ht h15 hp

end Benchmarks.UniswapV4PoolManager
