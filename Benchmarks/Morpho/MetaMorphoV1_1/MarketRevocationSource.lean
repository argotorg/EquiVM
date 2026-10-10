import Benchmarks.Morpho.MetaMorphoV1_1.CuratorGuardianSource
import Benchmarks.Morpho.MetaMorphoV1_1.MarketRevocationMutation
import Benchmarks.Morpho.MetaMorphoV1_1.RevocationSource

/-! Source bodies for cap and market-removal revocations. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

def marketRevocationBase (cap : Bool) : Ident := if cap then "pendingCap" else "config"
def marketRevocationRef (cap : Bool) : StorageRef :=
  if cap then ⟨"pendingCap", [.mindex (.var "id")]⟩
  else ⟨"config", [.mindex (.var "id"), .field "removableAt"]⟩
def marketRevocationEvent (cap : Bool) : Ident :=
  if cap then "RevokePendingCap" else "RevokePendingMarketRemoval"
def marketRevocationSlot (cap : Bool) (id : UInt256) : UInt256 :=
  solcMappingSlot (if cap then ⟨16⟩ else ⟨13⟩) id
def marketRevocationWord (cap : Bool) (old : UInt256) : UInt256 :=
  if cap then ⟨0⟩ else UInt256.land (UInt256.ofNat (2 ^ 192 - 1)) old
def marketRevocationState (cap : Bool) (evm : EVM.State) (id : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (marketRevocationSlot cap id)
    (marketRevocationWord cap
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (marketRevocationSlot cap id)))

def marketRevocationBody (cap : Bool) : List Stmt :=
  [.require (.binary .eq (.env .callvalue) (.intLit 0)),
    .letDecl "__calldata" (some .bytes) (.env .msgData),
    .require (.binary .lt (.arrayLength .localVar ⟨"__calldata", []⟩)
      (.intLit (Int.ofNat (2 ^ 255 + 4)))),
    .internalCall "_checkCuratorOrGuardianRole" [] "__role", .delete (marketRevocationRef cap),
    .internalCall "_msgSender" [] "__c4",
    .emit (marketRevocationEvent cap) [.var "__c4", .var "id"]]

theorem marketRevocationPrefix (cap : Bool) (evm : EVM.State) (locals imms : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hrole : curatorGuardianAllowed evm) :
    ABlock config evm { contract := contract, locals := locals, immutables := imms }
      (marketRevocationBody cap) (revocationFrame evm locals imms)
      [.delete (marketRevocationRef cap), .internalCall "_msgSender" [] "__c4",
        .emit (marketRevocationEvent cap) [.var "__c4", .var "id"]] := by
  constructor
  intro result htail
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  exact ExecBlock.consNormal (curatorGuardianCall evm _ imms "__role" hrole) htail

theorem marketRevocationDelete (cap : Bool) (evm : EVM.State) (locals imms : Store)
    (bs : List UInt8) (id : UInt256) (hlen : bs.length = 32)
    (hbase : locals.get? (marketRevocationBase cap) = none)
    (hget : locals.get? "id" = some (.fixedBytes abiBytes32Width bs))
    (hkey : keyValueToWord (.fixedBytes abiBytes32Width bs) = id) :
    deleteStorage? config (revocationFrame evm locals imms) evm (marketRevocationRef cap) =
      .ok (marketRevocationState cap evm id) := by
  simp only [Std.HashMap.get?_eq_getElem?] at hbase hget
  cases cap
  · exact deleteStorage_configRemovableAt evm _ imms bs id hlen
      (by simpa [revocationFrame, marketRevocationBase] using hbase)
      (by simpa [revocationFrame, Std.HashMap.getElem?_insert] using hget) hkey
  · exact deleteStorage_pendingCap evm _ imms bs id hlen
      (by simpa [revocationFrame, marketRevocationBase] using hbase)
      (by simpa [revocationFrame, Std.HashMap.getElem?_insert] using hget) hkey

theorem marketRevocationBodyReturns (cap : Bool) (evm : EVM.State) (locals imms : Store)
    (bs : List UInt8) (id : UInt256) (hlen : bs.length = 32)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hrole : curatorGuardianAllowed evm)
    (hbase : locals.get? (marketRevocationBase cap) = none)
    (hget : locals.get? "id" = some (.fixedBytes abiBytes32Width bs))
    (hkey : keyValueToWord (.fixedBytes abiBytes32Width bs) = id) :
    ∃ final, ExecTransitionBody config contract evm locals (marketRevocationBody cap)
      (.returned final (marketRevocationState cap evm id) none) imms := by
  refine ⟨{
    contract := contract
    locals := (revocationFrame evm locals imms).locals.insert "__c4"
      (.address (marketRevocationState cap evm id).executionEnv.source)
    immutables := imms }, ExecFuncBody.execBlockOK ?_⟩
  apply (marketRevocationPrefix cap evm locals imms hwv hhi hrole).run
  refine ExecBlock.consNormal (ExecStmt.delete
    (marketRevocationDelete cap evm locals imms bs id hlen hbase hget hkey)) ?_
  refine ExecBlock.consNormal
    (internalCallReturnExpr (retTy := [.elem .address]) (expr := .env .caller)
      (value := .address (marketRevocationState cap evm id).executionEnv.source)
      (by rfl) (by simp only [evalExpr?, envValue, pure])) ?_
  apply (ABlock.start.emitStep
    (vals := [.address (marketRevocationState cap evm id).executionEnv.source,
      .fixedBytes abiBytes32Width bs]) ?_).run
  · exact ExecBlock.nil
  · simp only [Std.HashMap.get?_eq_getElem?] at hget
    simp [evalExprs?, evalExpr?, revocationFrame, Std.HashMap.getElem?_insert, hget,
      EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem marketRevocationBodyStatic (cap : Bool) (evm : EVM.State) (locals imms : Store)
    (bs : List UInt8) (id : UInt256) (hlen : bs.length = 32)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hrole : curatorGuardianAllowed evm)
    (hbase : locals.get? (marketRevocationBase cap) = none)
    (hget : locals.get? "id" = some (.fixedBytes abiBytes32Width bs))
    (hkey : keyValueToWord (.fixedBytes abiBytes32Width bs) = id)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm locals (marketRevocationBody cap)
      .staticViolation imms := by
  apply ExecFuncBody.execBlockStatic
  apply (marketRevocationPrefix cap evm locals imms hwv hhi hrole).run
  exact ExecBlock.consStatic (ExecStmt.deleteStatic
    (marketRevocationDelete cap evm locals imms bs id hlen hbase hget hkey) hperm)

theorem marketRevocationBodyRevertsRole (cap : Bool) (evm : EVM.State) (locals imms : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hrole : ¬ curatorGuardianAllowed evm) :
    ExecTransitionBody config contract evm locals (marketRevocationBody cap) .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  exact ExecBlock.consRevert (curatorGuardianCallReverts evm _ imms "__role" hrole)

end Benchmarks.Morpho.MetaMorphoV1_1
