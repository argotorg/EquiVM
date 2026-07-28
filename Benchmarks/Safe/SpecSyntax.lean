import Benchmarks.Safe.Spec
import Solm.Notation

/-!
# Safe spec in the Solidity-faithful Solm frontend

The whole Safe benchmark spec, written with `solidity%` and proven definitionally equal to the
AST spec in `Benchmarks/Safe/Spec.lean`.

Notes mirroring the AST spec:
* EIP-712 typehashes, the EIP-1271 magic value, and the guard interface ids are the surface
  `bytesN(0x…)` fixed-bytes literals; `abi.encodePacked` operands carry their ABI types as `T(e)`
  annotations (`uint256(uint256(x))` when the spec casts inside the pair).
* The ecrecover and P-256 precompile calls target cast addresses (`address(1)`, `address(256)`),
  which the surface low-level call cannot express, so those two statements are spliced; their
  binders are then referenced via `${…}`.  The `"\x19Ethereum Signed Message:\n32"` prefix reuses
  the spec's `ethSignPrefix` (non-UTF-8 bytes), and the EIP-7702 code-prefix probe's
  `0xef0100` literal is spliced inside the surface `extCodePrefix(…) == …` comparison.
* Function and transition order match `contract.functions` / `contract.transitions` exactly.
* The fallback declares its `bytes` return type with the surface `returns (bytes)` clause.
-/

open Solm Solm.Notation

namespace Benchmarks.Safe.Syntax

def contractSyntax : ContractDecl :=
  solidity% contract Safe {
    address singleton;
    mapping(address => address) modules;
    mapping(address => address) owners;
    uint256 ownerCount;
    uint256 threshold;
    uint256 nonce;
    bytes32 _deprecatedDomainSeparator;
    mapping(bytes32 => uint256) signedMessages;
    mapping(address => mapping(bytes32 => uint256)) approvedHashes;
    address _fallbackHandler;
    address _guard;
    address _moduleGuard;
    mapping(uint256 => uint256) _rawStorage;

    constructor() {
      threshold = 1;
    }

    receive() external payable { }

    fallback(bytes calldata) external returns (bytes) {
      address handler = _fallbackHandler;
      if (handler == address(0)) {
        return "";
      } else {
        (bool handlerSuccess, bytes memory handlerReturn) =
          handler.call(abi.encodePacked(bytes(calldata), address(msg.sender)));
        require(handlerSuccess);
        return handlerReturn;
      }
    }

    function _add(uint256 x, uint256 y) internal returns (uint256) {
      return ((x + y) as uint256);
    }

    function _sub(uint256 x, uint256 y) internal returns (uint256) {
      return ((x - y) as uint256);
    }

    function _mul(uint256 x, uint256 y) internal returns (uint256) {
      return ((x * y) as uint256);
    }

    function execute(address «to», uint256 value, bytes data, uint8 operation, uint256 txGas)
        internal returns (bool) {
      if (operation == 1) {
        (bool success, bytes memory returnData) = «to».delegatecall(data);
      } else {
        (bool success, bytes memory returnData) = «to».call{value: value}(data);
      }
      return success;
    }

    function transferToken(address token, address receiver, uint256 amount)
        internal returns (bool) {
      (bool tokenSuccess, bytes memory tokenData) =
        token.call(abi.encodeWithSelector(transfer, receiver, amount));
      return tokenData.length == 0 ? tokenSuccess :
        tokenData.length == 32 ? tokenSuccess && abi.decode(tokenData, (uint256)) != 0 : false;
    }

    function handlePayment(uint256 gasUsed, uint256 baseGas, uint256 gasPrice, address gasToken,
        address refundReceiver) internal returns (uint256) {
      address receiver = refundReceiver == address(0) ? tx.origin : refundReceiver;
      var gasTotal = _add(gasUsed, baseGas);
      if (gasToken == address(0)) {
        var payment = _mul(gasTotal, gasPrice < tx.gasprice ? gasPrice : tx.gasprice);
        (bool refundSuccess, bytes memory refundData) = receiver.call{value: payment}("");
        require(refundSuccess);
      } else {
        var payment = _mul(gasTotal, gasPrice);
        var transferred = transferToken(gasToken, receiver, payment);
        require(transferred);
      }
      return payment;
    }

    function requireCanAddOwner(address owner) internal {
      require(owner != address(0) && owner != address(1) &&
        (owner != address(this) ||
          extCodePrefix(address(this), 3) == ${Expr.bytesLit ⟨#[0xef, 0x01, 0x00]⟩}));
      require(owners[owner] == address(0));
    }

    function requireCanRemoveOwner(address prevOwner, address owner) internal {
      require(owner != address(0) && owner != address(1) &&
        (owner != address(this) ||
          extCodePrefix(address(this), 3) == ${Expr.bytesLit ⟨#[0xef, 0x01, 0x00]⟩}));
      require(owners[prevOwner] == owner);
    }

    function changeThresholdBody(uint256 _threshold) internal {
      require(_threshold <= ownerCount);
      require(_threshold != 0);
      threshold = _threshold;
    }

    function setupOwners(address[] _owners, uint256 _threshold) internal {
      require(threshold == 0);
      require(_threshold <= _owners.length);
      require(_threshold != 0);
      address currentOwner = address(1);
      uint256 ownersLength = _owners.length;
      uint256 i = 0;
      while (i < ownersLength) {
        address owner = _owners[i];
        require(owner != currentOwner);
        var _ok = requireCanAddOwner(owner);
        owners[currentOwner] = owner;
        currentOwner = owner;
        i = ((i + 1) as uint256);
      }
      owners[currentOwner] = address(1);
      ownerCount = ownersLength;
      threshold = _threshold;
    }

    function internalSetFallbackHandler(address handler) internal {
      require(handler != address(this));
      _fallbackHandler = handler;
    }

    function setupModules(address «to», bytes data) internal {
      require(modules[address(1)] == address(0));
      modules[address(1)] = address(1);
      if («to» != address(0)) {
        require(«to».code.length > 0);
        var setupSuccess = execute(«to», 0, data, 1, type(uint256).max);
        require(setupSuccess);
      }
    }

    function preModuleExecution(address «to», uint256 value, bytes data, uint8 operation)
        internal returns (address, bytes32) {
      address guard = _moduleGuard;
      bytes32 guardHash = bytes32(0);
      require(msg.sender != address(1) && modules[msg.sender] != address(0));
      if (guard != address(0)) {
        var guardHashCall = guard.checkModuleTransaction(«to», value, data, operation, msg.sender);
        guardHash = guardHashCall;
      }
      return (guard, guardHash);
    }

    function postModuleExecution(address guard, bytes32 guardHash, bool success) internal {
      if (guard != address(0)) {
        require(guard.code.length > 0);
        var _after = guard.checkAfterModuleExecution(guardHash, success);
      }
    }

    function validateContractSignature(address owner, bytes32 dataHash, bytes signature)
        internal returns (bool) {
      (bool sigSuccess, bytes memory sigResult) =
        owner.staticcall(abi.encodeWithSelector(isValidSignature, dataHash, signature));
      return sigSuccess && sigResult.length == 32 &&
        abi.decode(sigResult, (bytes32)) ==
          bytes32(0x1626ba7e00000000000000000000000000000000000000000000000000000000);
    }

    function checkContractSignature(address owner, bytes32 dataHash, bytes signatures,
        uint256 offset) internal {
      var signatureDataStart = _add(offset, 32);
      require(signatureDataStart <= signatures.length);
      uint256 contractSignatureLen = abi.decode(signatures[offset : offset + 32], (uint256));
      var signatureDataEnd = _add(signatureDataStart, contractSignatureLen);
      require(signatureDataEnd <= signatures.length);
      bytes memory contractSignature = signatures[signatureDataStart : signatureDataEnd];
      var valid = validateContractSignature(owner, dataHash, contractSignature);
      require(valid);
    }

    function p256Verify(bytes32 h, bytes32 r, bytes32 s, uint256 qx, uint256 qy)
        internal returns (bool) {
      ${[Stmt.lowLevelCall p256Precompile (.intLit 0)
          (.abiEncodePacked
            [ (Benchmarks.Safe.bytes32, .var "h"), (Benchmarks.Safe.bytes32, .var "r"),
              (Benchmarks.Safe.bytes32, .var "s"),
              (Benchmarks.Safe.uint256, .var "qx"), (Benchmarks.Safe.uint256, .var "qy") ])
          "p256Success" "p256Result" false]}
      return ${Expr.var "p256Success"} && ${localLength "p256Result"} == 32 &&
        abi.decode(${Expr.var "p256Result"}, (uint256)) == 1;
    }

    function ecrecoverAddress(bytes32 digest, uint8 v, bytes32 r, bytes32 s)
        internal returns (address) {
      ${[Stmt.lowLevelCall ecrecoverPrecompile (.intLit 0) ecrecoverCalldataExpr
          "ecrecoverSuccess" "ecrecoverData" false]}
      require(${Expr.var "ecrecoverSuccess"});
      return ${localLength "ecrecoverData"} == 0 ? address(0) :
        abi.decode(${Expr.var "ecrecoverData"}, (address));
    }

    function checkNSignaturesImpl(address executor, bytes32 dataHash, bytes signatures,
        uint256 requiredSignatures) internal {
      var requiredBytes = _mul(requiredSignatures, 65);
      require(signatures.length >= requiredBytes);
      address lastOwner = address(0);
      address currentOwner = address(0);
      uint256 i = 0;
      while (i < requiredSignatures) {
        uint256 signatureOffset = 65 * i;
        bytes32 r = abi.decode(signatures[signatureOffset : signatureOffset + 32], (bytes32));
        bytes32 s =
          abi.decode(signatures[signatureOffset + 32 : signatureOffset + 32 + 32], (bytes32));
        uint8 v = uint8(signatures[signatureOffset + 64]);
        if (v == 0) {
          currentOwner = address(uint256(r));
          uint256 contractOffset = uint256(s);
          require(contractOffset >= requiredBytes);
          var _contractSigOk =
            checkContractSignature(currentOwner, dataHash, signatures, contractOffset);
        } else if (v == 1) {
          currentOwner = address(uint256(r));
          require(executor == currentOwner || approvedHashes[currentOwner][dataHash] != 0);
        } else if (v == 2) {
          currentOwner = address(uint256(r));
          uint256 p256Offset = uint256(s);
          require(p256Offset >= requiredBytes);
          var p256End = _add(p256Offset, 128);
          require(p256End <= signatures.length);
          bytes32 p256r = abi.decode(signatures[p256Offset : p256Offset + 32], (bytes32));
          bytes32 p256s =
            abi.decode(signatures[p256Offset + 32 : p256Offset + 32 + 32], (bytes32));
          uint256 qx = abi.decode(signatures[p256Offset + 64 : p256Offset + 64 + 32], (uint256));
          uint256 qy = abi.decode(signatures[p256Offset + 96 : p256Offset + 96 + 32], (uint256));
          address signerAddress =
            address(uint256(keccak256(abi.encodePacked(uint256(qx), uint256(qy)))));
          var p256Ok = p256Verify(dataHash, p256r, p256s, qx, qy);
          require(currentOwner == signerAddress && p256Ok);
        } else if (v > 30) {
          bytes32 ethSignedHash =
            keccak256(abi.encodePacked(bytes(${ethSignPrefix}), bytes32(dataHash)));
          var recoveredOwner = ecrecoverAddress(ethSignedHash, (v - 4) as uint8, r, s);
          currentOwner = recoveredOwner;
        } else {
          var recoveredOwner = ecrecoverAddress(dataHash, v, r, s);
          currentOwner = recoveredOwner;
        }
        require(currentOwner > lastOwner && owners[currentOwner] != address(0) &&
          currentOwner != address(1));
        lastOwner = currentOwner;
        i = ((i + 1) as uint256);
      }
    }

    function checkSignaturesImpl(address executor, bytes32 dataHash, bytes signatures) internal {
      uint256 _threshold = threshold;
      require(_threshold != 0);
      var _checked = checkNSignaturesImpl(executor, dataHash, signatures, _threshold);
    }

    function VERSION() external returns (string) {
      return "1.5.0";
    }

    function addOwnerWithThreshold(address owner, uint256 _threshold) external {
      require(msg.sender == address(this));
      var _ok = requireCanAddOwner(owner);
      owners[owner] = owners[address(1)];
      owners[address(1)] = owner;
      ownerCount = ((ownerCount + 1) as uint256);
      if (threshold != _threshold) {
        var _thresholdChanged = changeThresholdBody(_threshold);
      }
    }

    function approveHash(bytes32 hashToApprove) external {
      require(owners[msg.sender] != address(0));
      approvedHashes[msg.sender][hashToApprove] = 1;
    }

    function approvedHashes(address arg0, bytes32 arg1) external returns (uint256) {
      return approvedHashes[arg0][arg1];
    }

    function changeThreshold(uint256 _threshold) external {
      require(msg.sender == address(this));
      var _ok = changeThresholdBody(_threshold);
    }

    function checkNSignatures(bytes32 dataHash, bytes data, bytes signatures,
        uint256 requiredSignatures) external {
      var _checked = checkNSignaturesImpl(msg.sender, dataHash, signatures, requiredSignatures);
    }

    function checkNSignatures(address executor, bytes32 dataHash, bytes signatures,
        uint256 requiredSignatures) external {
      var _checked = checkNSignaturesImpl(executor, dataHash, signatures, requiredSignatures);
    }

    function checkSignatures(bytes32 dataHash, bytes data, bytes signatures) external {
      var _checked = checkSignaturesImpl(msg.sender, dataHash, signatures);
    }

    function checkSignatures(address executor, bytes32 dataHash, bytes signatures) external {
      var _checked = checkSignaturesImpl(executor, dataHash, signatures);
    }

    function disableModule(address prevModule, address «module») external {
      require(msg.sender == address(this));
      require(«module» != address(0) && «module» != address(1));
      require(modules[prevModule] == «module»);
      modules[prevModule] = modules[«module»];
      modules[«module»] = address(0);
    }

    function domainSeparator() external returns (bytes32) {
      return keccak256(abi.encodePacked(
        bytes32(bytes32(0x47e79534a245952e8b16893a336b85a3d9ea9fa8c573f3d803afb92a79469218)),
        uint256(block.chainid),
        uint256(uint256(this))));
    }

    function enableModule(address «module») external {
      require(msg.sender == address(this));
      require(«module» != address(0) && «module» != address(1));
      require(modules[«module»] == address(0));
      modules[«module»] = modules[address(1)];
      modules[address(1)] = «module»;
    }

    function execTransaction(address «to», uint256 value, bytes data, uint8 operation,
        uint256 safeTxGas, uint256 baseGas, uint256 gasPrice, address gasToken,
        address refundReceiver, bytes signatures) external payable returns (bool) {
      require(operation <= 1);
      uint256 nonceBefore = nonce;
      bytes32 txHash = keccak256(abi.encodePacked(
        bytes2(bytes2(0x1901)),
        bytes32(keccak256(abi.encodePacked(
          bytes32(bytes32(0x47e79534a245952e8b16893a336b85a3d9ea9fa8c573f3d803afb92a79469218)),
          uint256(block.chainid),
          uint256(uint256(this))))),
        bytes32(keccak256(abi.encodePacked(
          bytes32(bytes32(0xbb8310d486368db6bd6f849402fdd73ad53d316b5a4b2644ad6efe0f941286d8)),
          uint256(uint256(«to»)),
          uint256(value),
          bytes32(keccak256(data)),
          uint256(operation),
          uint256(safeTxGas),
          uint256(baseGas),
          uint256(gasPrice),
          uint256(uint256(gasToken)),
          uint256(uint256(refundReceiver)),
          uint256(nonceBefore))))));
      nonce = ((nonceBefore + 1) as uint256);
      var _sigOk = checkSignaturesImpl(msg.sender, txHash, signatures);
      address guard = _guard;
      if (guard != address(0)) {
        require(guard.code.length > 0);
        var _guardChecked = guard.checkTransaction(«to», value, data, operation, safeTxGas,
          baseGas, gasPrice, gasToken, refundReceiver, signatures, msg.sender);
      }
      uint256 gasForCheck = gasleft();
      require(gasForCheck >=
        ((((safeTxGas << 6) / 63 > ((safeTxGas + 2500) as uint256) ?
            (safeTxGas << 6) / 63 : ((safeTxGas + 2500) as uint256)) + 500) as uint256));
      uint256 gasBefore = gasleft();
      uint256 txGasLeft = gasleft();
      var success = execute(«to», value, data, operation,
        gasPrice == 0 ? ((txGasLeft - 2500) as uint256) : safeTxGas);
      uint256 gasAfter = gasleft();
      var gasUsed = _sub(gasBefore, gasAfter);
      require(success || safeTxGas != 0 || gasPrice != 0);
      uint256 payment = 0;
      if (gasPrice > 0) {
        var paymentCall = handlePayment(gasUsed, baseGas, gasPrice, gasToken, refundReceiver);
        payment = paymentCall;
      }
      if (guard != address(0)) {
        require(guard.code.length > 0);
        var _guardAfter = guard.checkAfterExecution(txHash, success);
      }
      return success;
    }

    function execTransactionFromModule(address «to», uint256 value, bytes data, uint8 operation)
        external returns (bool) {
      require(operation <= 1);
      var pre = preModuleExecution(«to», value, data, operation);
      var success = execute(«to», value, data, operation, type(uint256).max);
      var _post = postModuleExecution(pre.0, pre.1, success);
      return success;
    }

    function execTransactionFromModuleReturnData(address «to», uint256 value, bytes data,
        uint8 operation) external returns (bool, bytes) {
      require(operation <= 1);
      var pre = preModuleExecution(«to», value, data, operation);
      if (operation == 1) {
        (bool success, bytes memory returnData) = «to».delegatecall(data);
      } else {
        (bool success, bytes memory returnData) = «to».call{value: value}(data);
      }
      var _post = postModuleExecution(pre.0, pre.1, success);
      return (success, returnData);
    }

    function getModulesPaginated(address start, uint256 pageSize)
        external returns (address[], address) {
      require(start == address(1) || (modules[start] != address(0) && start != address(1)));
      require(pageSize != 0);
      uint256 moduleCount = 0;
      address next = modules[start];
      address last = address(0);
      while ((next != address(0) && next != address(1)) && moduleCount < pageSize) {
        last = next;
        next = modules[next];
        moduleCount = ((moduleCount + 1) as uint256);
      }
      if (next != address(1)) {
        require(moduleCount > 0);
        next = last;
      }
      address[] memory array = new address[](moduleCount);
      uint256 fill = 0;
      address current = modules[start];
      while (fill < moduleCount) {
        array[fill] = current;
        current = modules[current];
        fill = ((fill + 1) as uint256);
      }
      return (array, next);
    }

    function getOwners() external returns (address[]) {
      address[] memory array = new address[](ownerCount);
      uint256 index = 0;
      address currentOwner = owners[address(1)];
      while (currentOwner != address(1)) {
        array[index] = currentOwner;
        currentOwner = owners[currentOwner];
        index = ((index + 1) as uint256);
      }
      return array;
    }

    function getStorageAt(uint256 offset, uint256 length) external returns (bytes) {
      bytes memory result = "";
      uint256 index = 0;
      while (index < length) {
        result = abi.encodePacked(bytes(result), uint256(_rawStorage[offset + index]));
        index = ((index + 1) as uint256);
      }
      return result;
    }

    function getThreshold() external returns (uint256) {
      return threshold;
    }

    function getTransactionHash(address «to», uint256 value, bytes data, uint8 operation,
        uint256 safeTxGas, uint256 baseGas, uint256 gasPrice, address gasToken,
        address refundReceiver, uint256 _nonce) external returns (bytes32) {
      require(operation <= 1);
      return keccak256(abi.encodePacked(
        bytes2(bytes2(0x1901)),
        bytes32(keccak256(abi.encodePacked(
          bytes32(bytes32(0x47e79534a245952e8b16893a336b85a3d9ea9fa8c573f3d803afb92a79469218)),
          uint256(block.chainid),
          uint256(uint256(this))))),
        bytes32(keccak256(abi.encodePacked(
          bytes32(bytes32(0xbb8310d486368db6bd6f849402fdd73ad53d316b5a4b2644ad6efe0f941286d8)),
          uint256(uint256(«to»)),
          uint256(value),
          bytes32(keccak256(data)),
          uint256(operation),
          uint256(safeTxGas),
          uint256(baseGas),
          uint256(gasPrice),
          uint256(uint256(gasToken)),
          uint256(uint256(refundReceiver)),
          uint256(_nonce))))));
    }

    function isModuleEnabled(address «module») external returns (bool) {
      return modules[«module»] != address(0) && «module» != address(1);
    }

    function isOwner(address owner) external returns (bool) {
      return owners[owner] != address(0) && owner != address(1);
    }

    function nonce() external returns (uint256) {
      return nonce;
    }

    function removeOwner(address prevOwner, address owner, uint256 _threshold) external {
      require(msg.sender == address(this));
      ownerCount = ((ownerCount - 1) as uint256);
      require(ownerCount >= _threshold);
      var _ok = requireCanRemoveOwner(prevOwner, owner);
      owners[prevOwner] = owners[owner];
      owners[owner] = address(0);
      if (threshold != _threshold) {
        var _thresholdChanged = changeThresholdBody(_threshold);
      }
    }

    function setFallbackHandler(address handler) external {
      require(msg.sender == address(this));
      var _ok = internalSetFallbackHandler(handler);
    }

    function setGuard(address guard) external {
      require(msg.sender == address(this));
      if (guard != address(0)) {
        var supported = guard.supportsInterface{view}(bytes4(0xe6d7a83a));
        require(supported);
      }
      _guard = guard;
    }

    function setModuleGuard(address moduleGuard) external {
      require(msg.sender == address(this));
      if (moduleGuard != address(0)) {
        var supported = moduleGuard.supportsInterface{view}(bytes4(0x58401ed8));
        require(supported);
      }
      _moduleGuard = moduleGuard;
    }

    function setup(address[] _owners, uint256 _threshold, address «to», bytes data,
        address fallbackHandler, address paymentToken, uint256 payment,
        address paymentReceiver) external {
      var _ownersSetup = setupOwners(_owners, _threshold);
      if (fallbackHandler != address(0)) {
        var _fallbackSet = internalSetFallbackHandler(fallbackHandler);
      }
      var _modulesSetup = setupModules(«to», data);
      if (payment > 0) {
        var _paymentDone = handlePayment(payment, 0, 1, paymentToken, paymentReceiver);
      }
    }

    function signedMessages(bytes32 arg0) external returns (uint256) {
      return signedMessages[arg0];
    }

    function simulateAndRevert(address targetContract, bytes calldataPayload) external {
      (bool simulateSuccess, bytes memory simulateReturn) =
        targetContract.delegatecall(calldataPayload);
      require(false);
    }

    function swapOwner(address prevOwner, address oldOwner, address newOwner) external {
      require(msg.sender == address(this));
      var _canAdd = requireCanAddOwner(newOwner);
      var _canRemove = requireCanRemoveOwner(prevOwner, oldOwner);
      owners[newOwner] = owners[oldOwner];
      owners[prevOwner] = newOwner;
      owners[oldOwner] = address(0);
    }
  }

theorem contractSyntax_eq : contractSyntax = Benchmarks.Safe.contract := by rfl

end Benchmarks.Safe.Syntax
