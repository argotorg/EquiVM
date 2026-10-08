import Solm.Interp
import Solm.MetaSolidityLayout
import Solm.Notation

/-! Internal parameters and returns carry storage types; references retain their aliases.
These checks exercise notation, layout resolution, argument binding and execution together. -/

namespace Solm.FunctionReferenceTests

private def contract : ContractDecl := solidity% contract References {
  struct State { uint128 value; mapping(int24 => uint256) ticks; }
  struct Plain { uint256 value; uint256 other; }
  mapping(bytes32 => State) pools;
  Plain plain;
  State[] states;
  uint256[] data;

  function exercise() external returns (uint256, uint256, uint256, uint256) {
    State storage selected = getPool(bytes32(7));
    var ignored = forward(selected, selected, 4);
    var pair = getPair(selected);
    State storage same = pair.0;
    same.value += pair.1;
    var unused = bumpTicks(same.ticks);
    Plain memory snapshot = plain;
    var changed = changeValue(snapshot);
    return (pools[bytes32(7)].value, pools[bytes32(7)].ticks[-2], plain.value, changed);
  }
  function getPool(bytes32 id) internal returns (State storage) {
    return pools[id];
  }
  function forward(State storage a, State storage b, uint256 n) internal {
    var ignored = writeBoth(a, b, n);
  }
  function writeBoth(State storage a, State storage b, uint256 n) internal {
    a.value = uint128(n);
    b.value += 3;
  }
  function getPair(State storage a) internal returns (State storage, uint256) {
    return (a, 5);
  }
  function bumpTicks(mapping(int24 => uint256) storage ticks) internal {
    ticks[-2] += 9;
  }
  function changeValue(Plain memory p) internal returns (uint256) {
    p.value = 19;
    return p.value;
  }
  function bounds() external {
    var ignored = forward(states[0], states[0], 1);
  }
  function fail() external {
    var ignored = reject(pools[bytes32(7)]);
  }
  function reject(State storage a) internal {
    a.value = 1;
    require(false);
  }
  function arrayExercise() external returns (uint256) {
    uint256[] storage a = numbers();
    var ignored = append(a);
    return data[0];
  }
  function numbers() internal returns (uint256[] storage) { return data; }
  function append(uint256[] storage a) internal { a.push(23); }
}

private def cfg : Config :=
  { storageBackend := solidityStorage! [contract.structs] [contract.storage]
    externalABI := defaultExternalCallABI
    selfDeployment := fun code _ => some code }

private def evm : EVM.State :=
  { (default : EVM.State) with
    executionEnv := { (default : Ethereum.ExecutionEnv) with codeOwner := .ofNat 256, perm := true }
    accountMap := (∅ : Ethereum.AccountMap).insert (.ofNat 256) default }

private def run (name : Ident) (state : EVM.State := evm) : Interp.Outcome :=
  match contract.transitions.find? (·.name == name) with
  | none => .stuck "missing test transition"
  | some t => (Interp.execTransitionBody 200 Interp.thetaOracle () cfg contract state ∅ t.body ∅).1

private def values : Interp.Outcome → Option (List Value)
  | .result (.returned _ _ vs) => vs
  | _ => none

-- The two parameters alias the same pool; forwarding and a mixed return preserve that alias.
-- The ordinary struct argument remains a value, and its mutation leaves storage unchanged.
#guard values (run "exercise") = some [.int 12, .int 9, .int 0, .int 19]
#guard (run "bounds").describe = "reverted"
#guard (run "fail").describe = "reverted"
#guard (run "exercise" { evm with executionEnv.perm := false }).describe = "staticViolation"
#guard values (run "arrayExercise") = some [.int 23]
#guard match ((contract.functions[1]!).params[0]!).ty with
  | .struct "State" _ => true
  | _ => false
#guard (contract.functions[0]!).returnType = [((contract.functions[1]!).params[0]!).ty]
#guard (contract.functions[4]!).params.map (·.ty) =
  [.mapping (.int (.sint ⟨24, by decide⟩)) (.elem (.int (.uint ⟨256, by decide⟩)))]

-- Existing hand-written ABI annotations still reduce definitionally after coercion.
example : StorageType.ofABI (.tuple [.elem .address, .dynamicArray (.elem .bool)]) =
    .tuple [.elem .address, .dynamicArray (.elem .bool)] := by rfl

/-- error: solm: storage reference type mismatch -/
#guard_msgs in
private def wrongReference : ContractDecl := solidity% contract WrongReference {
  uint128[] a;
  function f(uint256[] storage p) internal {}
  function go() external { var ignored = f(a); }
}

/-- error: solm: expected a persistent storage reference -/
#guard_msgs in
private def valueAsReference : ContractDecl := solidity% contract ValueAsReference {
  function f(uint256[] storage p) internal {}
  function go(uint256[] memory a) external { var ignored = f(a); }
}

/-- error: solm: external return types cannot be storage references -/
#guard_msgs in
private def externalReference : ContractDecl := solidity% contract ExternalReference {
  uint256[] a;
  function go() external returns (uint256[] storage) { return a; }
}

end Solm.FunctionReferenceTests
