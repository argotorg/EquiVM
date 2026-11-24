import Benchmarks.EAS.EAS.GetSchemaResult

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def getSchemaArgs (uid : UInt256) (heap : Nat) : Store :=
  (∅ : Store) |>.insert "$EAS.freeMemory" (.int (Int.ofNat heap)) |>.insert "uid" (wordBytes32Value uid)

theorem getSchema_lookup : lookupCallable? contract "_getSchema" = some getSchemaFunction.toCallable := rfl

theorem getSchema_bind (uid : UInt256) (heap : Nat) :
    bindParams? getSchemaFunction.params [wordBytes32Value uid,.int (Int.ofNat heap)] =
      some (getSchemaArgs uid heap) := rfl

theorem getSchemaBodySource {evm evm' : EVM.State} {uid : UInt256} {heap : Nat}
    {success : Bool} {out : ByteArray} (v : EASImmutables)
    (hc : callViaEVM fork evm v._schemaRegistry 0 (getSchemaPayload uid) (success,evm',out) false)
    (hout : out.size < 2^255) :
    if schemaCallValid heap success out then
      ∃ locals', ExecFuncBody fork config {contract := contract, locals := getSchemaArgs uid heap, immutables := immStore v}
        evm getSchemaFunction.body
        (.returned {contract := contract, locals := locals', immutables := immStore v}
          evm' (some [(decodedSchemaRecord out (schemaReturnOffset out)).value,.int (Int.ofNat (schemaFinalHeap heap out))]))
    else ExecFuncBody fork config {contract := contract, locals := getSchemaArgs uid heap, immutables := immStore v}
      evm getSchemaFunction.body .reverted := by
  have hp := getSchemaPrefixSource (cfg := config) (locals := getSchemaArgs uid heap) v (store_get_self _ _ _) hc
  have hok : (getSchemaPrefixLocals (getSchemaArgs uid heap) v uid success out).get? "ok" = some (.bool success) := by
    simp only [getSchemaPrefixLocals,store_get_ne _ _ (by decide : ("result" == "ok") = false),store_get_self]
  have hor : (getSchemaPrefixLocals (getSchemaArgs uid heap) v uid success out).get? "result" = some (.bytes out) := store_get_self _ _ _
  have hh : (getSchemaPrefixLocals (getSchemaArgs uid heap) v uid success out).get? "$EAS.freeMemory" =
      some (.int (Int.ofNat heap)) := by
    simp only [getSchemaPrefixLocals,getSchemaArgs,
      store_get_ne _ _ (by decide : ("result" == "$EAS.freeMemory") = false),
      store_get_ne _ _ (by decide : ("ok" == "$EAS.freeMemory") = false),
      store_get_ne _ _ (by decide : ("payload" == "$EAS.freeMemory") = false),
      store_get_ne _ _ (by decide : ("registry" == "$EAS.freeMemory") = false),
      store_get_ne _ _ (by decide : ("uid" == "$EAS.freeMemory") = false),store_get_self]
  have hr := getSchemaResultSource (fork := fork) (imms := immStore v) (evm := evm') hok hor hh hout
  by_cases hv : schemaCallValid heap success out
  · rw [if_pos hv] at hr ⊢
    refine ⟨getSchemaFinalLocals (getSchemaPrefixLocals (getSchemaArgs uid heap) v uid success out) heap out,?_⟩
    rw [getSchema_body]
    exact execFuncBody_append hp hr
  · rw [if_neg hv] at hr ⊢
    rw [getSchema_body]
    exact execFuncBody_append hp hr

end Benchmarks.EAS.EAS
