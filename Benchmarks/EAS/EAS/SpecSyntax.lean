import Solm.Notation
import ABI.Decode

/-!
# EAS v0.26 specification

Drafted from the pinned solc AST and retained for the 0.8.32 recompilation.
Explicit adapters model tuple decoding, resolver
ABI encoding, ETH refunds, EIP-712 hashing, and the address-1 precompile call.
The immutable hash words use uint256 internally, with explicit bytes32 casts at
hash and return boundaries, matching the proof generator's word valuation.
-/

open Solm Solm.Notation

namespace Benchmarks.EAS.EAS.Syntax

/-- Reject a deferred ABI failure exactly where the compiled body accesses that value. -/
private def checkedCalldata (value : Expr) : List Stmt :=
  [.require (.binary .ne value (.structLit ABI.Solc08Calldata.decodeFailureTag []))]

/-- The compiled allocator's free pointer is local to each EVM invocation. Thread it through
    internal calls only; external signatures and persistent storage are unaffected. -/
private def heapName : String := "$EAS.freeMemory"

private def packReturns : List Expr → Expr
  | [e] => e
  | es => .tupleLit es

mutual
  private def allocationStmt (functions : List String) (internal : Bool) : Stmt → List Stmt
    | .internalCall name args ret =>
      if functions.contains name then
        let pair := ret ++ "$allocation"
        [.internalCall name (args ++ [.var heapName]) pair,
         .letDecl ret none (.tupleGet (.var pair) 0),
         .assign .localVar { base := heapName } (.tupleGet (.var pair) 1)]
      else [.internalCall name args ret]
    | .return values =>
      [.return (if internal then [packReturns values, .var heapName] else values)]
    | .while cond body => [.while cond (allocationBody functions internal body)]
    | .for init cond post body => [.for (allocationBody functions internal init) cond
        (allocationBody functions internal post) (allocationBody functions internal body)]
    | .ite cond yes no => [.ite cond (allocationBody functions internal yes)
        (allocationBody functions internal no)]
    | stmt => [stmt]
  termination_by stmt => sizeOf stmt

  private def allocationBody (functions : List String) (internal : Bool) : Body → Body
    | [] => []
    | stmt :: rest => allocationStmt functions internal stmt ++ allocationBody functions internal rest
  termination_by body => sizeOf body
end

private abbrev withAllocator (contract : ContractDecl) : ContractDecl :=
  let functions := contract.functions.map (·.name)
  let word : ABI.ABIType := .elem (.int (.uint ⟨256, by decide⟩))
  { contract with
    functions := contract.functions.map fun fn =>
      let result := match fn.returnType with | [ty] => ty | ts => .tuple ts
      { fn with
        params := fn.params ++ [{ name := heapName, ty := word }]
        returnType := [result, word]
        body := allocationBody functions true fn.body ++ [.return [.tupleLit [], .var heapName]] }
    transitions := contract.transitions.map fun fn =>
      { fn with body := .letDecl heapName none (.intLit 224) :: allocationBody functions false fn.body }
    -- Canonical constructor input is one word. Its argument copy and two strings end at 512.
    ctor := { contract.ctor with
      body := .letDecl heapName none (.intLit 512) ::
        allocationBody functions false contract.ctor.body } }

private abbrev contractBody : ContractDecl := solidity% contract EAS {
  struct EIP712Signature {
    uint8 v;
    bytes32 r;
    bytes32 s;
  }

  struct Attestation {
    bytes32 uid;
    bytes32 schema;
    uint64 time;
    uint64 expirationTime;
    uint64 revocationTime;
    bytes32 refUID;
    address recipient;
    address attester;
    bool revocable;
    bytes data;
  }

  struct AttestationRequestData {
    address recipient;
    uint64 expirationTime;
    bool revocable;
    bytes32 refUID;
    bytes data;
    uint256 value;
  }

  struct AttestationRequest {
    bytes32 schema;
    AttestationRequestData data;
  }

  struct DelegatedAttestationRequest {
    bytes32 schema;
    AttestationRequestData data;
    EIP712Signature signature;
    address attester;
  }

  struct MultiAttestationRequest {
    bytes32 schema;
    AttestationRequestData[] data;
  }

  struct MultiDelegatedAttestationRequest {
    bytes32 schema;
    AttestationRequestData[] data;
    EIP712Signature[] signatures;
    address attester;
  }

  struct RevocationRequestData {
    bytes32 uid;
    uint256 value;
  }

  struct RevocationRequest {
    bytes32 schema;
    RevocationRequestData data;
  }

  struct DelegatedRevocationRequest {
    bytes32 schema;
    RevocationRequestData data;
    EIP712Signature signature;
    address revoker;
  }

  struct MultiRevocationRequest {
    bytes32 schema;
    RevocationRequestData[] data;
  }

  struct MultiDelegatedRevocationRequest {
    bytes32 schema;
    RevocationRequestData[] data;
    EIP712Signature[] signatures;
    address revoker;
  }

  struct SchemaRecord {
    bytes32 uid;
    address resolver;
    bool revocable;
    string schema;
  }

  struct AttestationsResult {
    uint256 usedValue;
    bytes32[] uids;
  }

  uint256 immutable _CACHED_DOMAIN_SEPARATOR;
  uint256 immutable _CACHED_CHAIN_ID;
  address immutable _CACHED_THIS;
  uint256 immutable _HASHED_NAME;
  uint256 immutable _HASHED_VERSION;
  uint256 immutable _TYPE_HASH;
  mapping(address => uint256) _nonces;
  address immutable _schemaRegistry;
  mapping(bytes32 => Attestation) _db;
  mapping(bytes32 => uint64) _timestamps;
  mapping(address => mapping(bytes32 => uint64)) _revocationsOffchain;

  event Attested(address indexed recipient, address indexed attester, bytes32 uid, bytes32 indexed schema);
  event Revoked(address indexed recipient, address indexed attester, bytes32 uid, bytes32 indexed schema);
  event Timestamped(bytes32 indexed data, uint64 indexed timestamp);
  event RevokedOffchain(address indexed revoker, bytes32 indexed data, uint64 indexed timestamp);

  function _allocate(uint256 size) internal {
    uint256 rounded = uint256(size + 31);
    rounded = rounded / 32 * 32;
    uint256 next = uint256(${Expr.var heapName} + rounded);
    require(next <= 18446744073709551615 && next >= ${Expr.var heapName});
    ${[Stmt.assign .localVar { base := heapName } (.var "next")]}
  }

  function _copyAttestationData(AttestationRequestData data) internal {
    var allocation = _allocate(192);
    bytes payload = data.4;
    require(payload.length <= 18446744073709551615);
    var allocation = _allocate(32 + (payload.length + 31) / 32 * 32);
  }

  function _copyAttestationArray(AttestationRequestData[] data) internal {
    require(data.length <= 18446744073709551615);
    var allocation = _allocate(32 + data.length * 32);
    uint256 i = 0;
    while (i < data.length) {
      var allocation = _copyAttestationData(data[i]);
      i = uint256(i + 1);
    }
  }

  function _copyStoredAttestation(bytes32 uid) internal returns (Attestation) {
    var allocation = _allocate(320);
    Attestation memory attestation = _db[uid];
    bytes payload = attestation.data;
    var allocation = _allocate(32 + (payload.length + 31) / 32 * 32);
    return attestation;
  }

  function _decodeAttestationData(AttestationRequestData data) internal returns (AttestationRequestData) {
    return AttestationRequestData({recipient: data.0, expirationTime: data.1, revocable: data.2,
      refUID: data.3, data: data.4, value: data.5});
  }

  function _decodeRevocationData(RevocationRequestData data) internal returns (RevocationRequestData) {
    return RevocationRequestData({uid: data.0, value: data.1});
  }

  function _decodeSignature(EIP712Signature signature) internal returns (EIP712Signature) {
    return EIP712Signature({v: signature.0, r: signature.1, s: signature.2});
  }

  function _calldataWord(uint256 offset) internal returns (uint256) {
    bytes input = msg.data;
    if (offset >= input.length) {
      return 0;
    }
    uint256 count = input.length - offset;
    if (count > 32) {
      count = 32;
    }
    bytes part = input[offset:offset + count];
    bytes padding = new bytes(32 - count);
    bytes word = abi.encodePacked(bytes(part), bytes(padding));
    return abi.decode(word, (uint256));
  }

  function _checkAttestationArrayCopy(uint256 index, uint256 length) internal {
    bytes input = msg.data;
    var root = _calldataWord(4);
    uint256 heads = uint256(root + 36);
    var relative = _calldataWord(uint256(heads + index * 32));
    uint256 request = uint256(heads + relative);
    var tail = _calldataWord(uint256(request + 32));
    uint256 data = uint256(request + tail + 32);
    require(uint256(data + length * 32) <= uint256(input.length));
    uint256 i = 0;
    while (i < length) {
      var offset = _calldataWord(uint256(data + i * 32));
      require(offset <= 18446744073709551615);
      i = uint256(i + 1);
    }
  }

  function _getSchema(bytes32 uid) internal returns (SchemaRecord) {
    address registry = _schemaRegistry;
    bytes payload = abi.encodePacked(bytes4(bytes4(0xa2ea7c6e)), bytes32(uid));
    (bool ok, bytes result) = registry.staticcall(payload);
    require(ok);
    var allocation = _allocate(result.length);
    var allocation = _allocate(128);
    var record = abi.decode(result, (SchemaRecord));
    string text = record.3;
    require(text.length <= 18446744073709551615);
    var allocation = _allocate(32 + (text.length + 31) / 32 * 32);
    return SchemaRecord({uid: record.0, resolver: record.1, revocable: record.2, schema: record.3});
  }

  function _encodeAttestation(Attestation attestation) internal returns (bytes) {
    bytes data = attestation.data;
    bytes padding = new bytes((32 - data.length % 32) % 32);
    return abi.encodePacked(bytes32(attestation.uid), bytes32(attestation.schema),
      uint256(attestation.time), uint256(attestation.expirationTime), uint256(attestation.revocationTime),
      bytes32(attestation.refUID), uint256(uint256(attestation.recipient)),
      uint256(uint256(attestation.attester)), uint256(attestation.revocable ? 1 : 0),
      uint256(320), uint256(data.length), bytes(data), bytes(padding));
  }

  function _encodeAttestations(Attestation[] attestations) internal returns (bytes) {
    bytes heads = new bytes(0);
    bytes tails = new bytes(0);
    uint256 offset = attestations.length * 32;
    uint256 i = 0;
    while (i < attestations.length) {
      var body = _encodeAttestation(attestations[i]);
      heads = abi.encodePacked(bytes(heads), uint256(offset));
      tails = abi.encodePacked(bytes(tails), bytes(body));
      offset = offset + body.length;
      i = i + 1;
    }
    return abi.encodePacked(uint256(attestations.length), bytes(heads), bytes(tails));
  }

  function _resolverOne(address resolver, Attestation attestation, bool revocation, uint256 value) internal returns (bool) {
    var body = _encodeAttestation(attestation);
    bytes4 selector = revocation ? bytes4(0xe49617e1) : bytes4(0xe60c3505);
    bytes payload = abi.encodePacked(bytes4(selector), uint256(32), bytes(body));
    (bool ok, bytes result) = resolver.call{value: value}(payload);
    require(ok);
    uint256 copied = result.length;
    if (copied > 32) { copied = 32; }
    var allocation = _allocate(copied);
    bool accepted = abi.decode(result, (bool));
    return accepted;
  }

  function _resolverMany(address resolver, Attestation[] attestations, uint256[] values, bool revocation, uint256 value) internal returns (bool) {
    var body = _encodeAttestations(attestations);
    bytes valuesBody = abi.encodePacked(uint256(values.length));
    uint256 i = 0;
    while (i < values.length) {
      valuesBody = abi.encodePacked(bytes(valuesBody), uint256(values[i]));
      i = i + 1;
    }
    bytes4 selector = revocation ? bytes4(0x88e5b2d9) : bytes4(0x91db0b7e);
    bytes payload = abi.encodePacked(bytes4(selector), uint256(64), uint256(64 + body.length), bytes(body), bytes(valuesBody));
    (bool ok, bytes result) = resolver.call{value: value}(payload);
    require(ok);
    uint256 copied = result.length;
    if (copied > 32) { copied = 32; }
    var allocation = _allocate(copied);
    bool accepted = abi.decode(result, (bool));
    return accepted;
  }

  constructor(address registry) {
    bytes32 hashedName = keccak256("EAS");
    bytes32 hashedVersion = keccak256("0.26");
    bytes32 typeHash = keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)");
    _HASHED_NAME = uint256(hashedName);
    _HASHED_VERSION = uint256(hashedVersion);
    _CACHED_CHAIN_ID = block.chainid;
    var domain = _buildDomainSeparator(typeHash, hashedName, hashedVersion);
    _CACHED_DOMAIN_SEPARATOR = uint256(domain);
    _CACHED_THIS = address(this);
    _TYPE_HASH = uint256(typeHash);
    require(registry != address(0));
    _schemaRegistry = registry;
  }

  function _attest(bytes32 schema, AttestationRequestData[] memory data, address attester, uint256 availableValue, bool last) internal returns (AttestationsResult) {
    var allocation = _allocate(128);
    uint256 length = data.length;
    bytes32[] empty = new bytes32[](0);
    AttestationsResult res = AttestationsResult({usedValue: 0, uids: empty});
    require(length <= 18446744073709551615);
    var allocation = _allocate(32 + length * 32);
    res.uids = new bytes32[](length);
    var schemaRecord = _getSchema(schema);
    require(schemaRecord.uid != bytes32(0));
    require(length <= 18446744073709551615);
    var allocation = _allocate(32 + length * 352);
    Attestation[] attestations = new Attestation[](length);
    require(length <= 18446744073709551615);
    var allocation = _allocate(32 + length * 32);
    uint256[] values = new uint256[](length);
    uint256 i = 0;
    while (i < length) {
      var request = _decodeAttestationData(data[i]);
      var __c1 = _time();
      require(!(((request.expirationTime != 0) && (request.expirationTime <= __c1))));
      require(!((!(schemaRecord.revocable) && request.revocable)));
      var __c2 = _time();
      var allocation = _allocate(320);
      Attestation memory attestation = Attestation({uid: bytes32(0), schema: schema, time: __c2, expirationTime: request.expirationTime, revocationTime: 0, refUID: request.refUID, recipient: request.recipient, attester: attester, revocable: request.revocable, data: request.data});
      bytes32 uid = bytes32(0);
      uint32 bump = 0;
      while (true) {
        var __c3 = _getUID(attestation, bump);
        uid = __c3;
        if (_db[uid].uid == bytes32(0)) {
          break;
        }
        bump = uint32(bump + 1);
      }
      attestation.uid = uid;
      _db[uid] = attestation;
      if (request.refUID != bytes32(0)) {
        var __c4 = isAttestationValid_body(request.refUID);
        require(__c4);
      }
      attestations[i] = attestation;
      values[i] = request.value;
      res.uids[i] = uid;
      emit Attested(request.recipient, attester, uid, schema);
      i = uint256(i + 1);
    }
    var __c5 = _resolveAttestations(schemaRecord, attestations, values, false, availableValue, last);
    res.usedValue = __c5;
    return res;
  }

  function _verifyAttest(DelegatedAttestationRequest memory request) internal {
    var data = _decodeAttestationData(request.data);
    var signature = _decodeSignature(request.signature);
    uint256 nonce = 0;
    nonce = _nonces[request.attester];
    _nonces[request.attester] = uint256(nonce + 1);
    var allocation = _allocate(288);
    bytes32 dataHash = keccak256(data.data);
    bytes payload = abi.encodePacked(bytes32(bytes32(0xdbfdf8dc2b135c26253e00d5b6cbe6f20457e003fd526d97cea183883570de61)), bytes32(request.schema), uint256(uint256(data.recipient)), uint256(data.expirationTime), uint256(data.revocable ? 1 : 0), bytes32(data.refUID), bytes32(dataHash), uint256(nonce));
    bytes32 structHash = keccak256(payload);
    var digest = _hashTypedDataV4(structHash);
    var __c0 = ECDSA_recover(digest, signature.v, signature.r, signature.s);
    require(__c0 == request.attester);
  }

  function _mergeUIDs(bytes32[][] memory uidLists, uint256 uidsCount) internal returns (bytes32[]) {
    require(uidsCount <= 18446744073709551615);
    var allocation = _allocate(32 + uidsCount * 32);
    bytes32[] uids = new bytes32[](uidsCount);
    uint256 currentIndex = 0;
    uint256 i = 0;
    while (i < uidLists.length) {
      bytes32[] memory currentUids = uidLists[i];
      uint256 j = 0;
      while (j < currentUids.length) {
        uids[currentIndex] = currentUids[j];
        j = uint256(j + 1);
        currentIndex = uint256(currentIndex + 1);
      }
      i = uint256(i + 1);
    }
    return uids;
  }

  function _revoke(bytes32 schema, RevocationRequestData[] memory data, address revoker, uint256 availableValue, bool last) internal returns (uint256) {
    var schemaRecord = _getSchema(schema);
    require(schemaRecord.uid != bytes32(0));
    uint256 length = data.length;
    require(length <= 18446744073709551615);
    var allocation = _allocate(32 + length * 352);
    Attestation[] attestations = new Attestation[](length);
    require(length <= 18446744073709551615);
    var allocation = _allocate(32 + length * 32);
    uint256[] values = new uint256[](length);
    uint256 i = 0;
    while (i < length) {
      var request = _decodeRevocationData(data[i]);
      Attestation storage attestation = _db[request.uid];
      require(attestation.uid != bytes32(0));
      require(attestation.schema == schema);
      require(attestation.attester == revoker);
      require(attestation.revocable);
      require(attestation.revocationTime == 0);
      var __c1 = _time();
      attestation.revocationTime = __c1;
      var copied = _copyStoredAttestation(request.uid);
      attestations[i] = copied;
      values[i] = request.value;
      emit Revoked(attestation.recipient, revoker, request.uid, attestation.schema);
      i = uint256(i + 1);
    }
    var __c2 = _resolveAttestations(schemaRecord, attestations, values, true, availableValue, last);
    return __c2;
  }

  function _verifyRevoke(DelegatedRevocationRequest memory request) internal {
    var data = _decodeRevocationData(request.data);
    var signature = _decodeSignature(request.signature);
    uint256 nonce = 0;
    nonce = _nonces[request.revoker];
    _nonces[request.revoker] = uint256(nonce + 1);
    var allocation = _allocate(160);
    bytes payload = abi.encodePacked(bytes32(bytes32(0xa98d02348410c9c76735e0d0bb1396f4015ac2bb9615f9c2611d19d7a8a99650)), bytes32(request.schema), bytes32(data.uid), uint256(nonce));
    bytes32 structHash = keccak256(payload);
    var digest = _hashTypedDataV4(structHash);
    var __c0 = ECDSA_recover(digest, signature.v, signature.r, signature.s);
    require(__c0 == request.revoker);
  }

  function _time() internal returns (uint64) {
    return uint64(block.timestamp);
  }

  function _timestamp(bytes32 data, uint64 time) internal {
    require(_timestamps[data] == 0);
    _timestamps[data] = time;
    emit Timestamped(data, time);
  }

  function _revokeOffchain(address revoker, bytes32 data, uint64 time) internal {
    mapping(bytes32 => uint64) storage revocations = _revocationsOffchain[revoker];
    require(revocations[data] == 0);
    revocations[data] = time;
    emit RevokedOffchain(revoker, data, time);
  }

  function _domainSeparatorV4() internal returns (bytes32) {
    if ((address(this) == _CACHED_THIS) && (block.chainid == _CACHED_CHAIN_ID)) {
      return bytes32(_CACHED_DOMAIN_SEPARATOR);
    } else {
      var __c0 = _buildDomainSeparator(bytes32(_TYPE_HASH), bytes32(_HASHED_NAME), bytes32(_HASHED_VERSION));
      return __c0;
    }
  }

  function _buildDomainSeparator(bytes32 typeHash, bytes32 nameHash, bytes32 versionHash) internal returns (bytes32) {
    var allocation = _allocate(192);
    return keccak256(abi.encodePacked(bytes32(typeHash), bytes32(nameHash), bytes32(versionHash), uint256(block.chainid), uint256(uint256(address(this)))));
  }

  function _getUID(Attestation memory attestation, uint32 bump) internal returns (bytes32) {
    bytes payload = attestation.data;
    var allocation = _allocate(157 + payload.length);
    return keccak256(abi.encodePacked(bytes32(attestation.schema), address(attestation.recipient), address(attestation.attester), uint64(attestation.time), uint64(attestation.expirationTime), bool(attestation.revocable), bytes32(attestation.refUID), bytes(attestation.data), uint32(bump)));
  }

  function isAttestationValid_body(bytes32 uid) internal returns (bool) {
    return _db[uid].uid != bytes32(0);
  }

  function _resolveAttestations(SchemaRecord memory schemaRecord, Attestation[] memory attestations, uint256[] memory values, bool isRevocation, uint256 availableValue, bool last) internal returns (uint256) {
    uint256 length = attestations.length;
    if (length == 1) {
      var __c0 = _resolveAttestation(schemaRecord, attestations[0], values[0], isRevocation, availableValue, last);
      return __c0;
    }
    address resolver = schemaRecord.resolver;
    if (resolver == address(0)) {
      uint256 i = 0;
      while (i < length) {
        require(values[i] == 0);
        i = uint256(i + 1);
      }
      return 0;
    }
    uint256 totalUsedValue = 0;
    uint256 i = 0;
    while (i < length) {
      uint256 value = values[i];
      if (value != 0) {
        var payableResult = resolver.isPayable{view}();
        var allocation = _allocate(32);
        require(payableResult);
      }
      require(value <= availableValue);
      availableValue = uint256(availableValue - value);
      totalUsedValue = uint256(totalUsedValue + value);
      i = uint256(i + 1);
    }
    if (isRevocation) {
      var __c2 = _resolverMany(resolver, attestations, values, true, totalUsedValue);
      require(__c2);
    } else {
      var __c3 = _resolverMany(resolver, attestations, values, false, totalUsedValue);
      require(__c3);
    }
    if (last) {
      var __c4 = _refund(availableValue);
    }
    return totalUsedValue;
  }

  function _hashTypedDataV4(bytes32 structHash) internal returns (bytes32) {
    var __c0 = _domainSeparatorV4();
    var __c1 = ECDSA_toTypedDataHash(__c0, structHash);
    return __c1;
  }

  function ECDSA_recover(bytes32 hash, uint8 v, bytes32 r, bytes32 s) internal returns (address) {
    var __c0 = ECDSA_tryRecover(hash, v, r, s);
    address recovered = __c0.0;
    uint8 error = __c0.1;
    var __c1 = ECDSA__throwError(error);
    return recovered;
  }

  function _resolveAttestation(SchemaRecord memory schemaRecord, Attestation memory attestation, uint256 value, bool isRevocation, uint256 availableValue, bool last) internal returns (uint256) {
    address resolver = schemaRecord.resolver;
    if (resolver == address(0)) {
      require(value == 0);
      return 0;
    }
    if (value != 0) {
      var payableResult = resolver.isPayable{view}();
      var allocation = _allocate(32);
      require(payableResult);
    }
    require(value <= availableValue);
    availableValue = uint256(availableValue - value);
    if (isRevocation) {
      var __c1 = _resolverOne(resolver, attestation, true, value);
      require(__c1);
    } else {
      var __c2 = _resolverOne(resolver, attestation, false, value);
      require(__c2);
    }
    if (last) {
      var __c3 = _refund(availableValue);
    }
    return value;
  }

  function _refund(uint256 remainingValue) internal {
    if (remainingValue > 0) {
      require(address(this).balance >= remainingValue);
      bytes empty = new bytes(0);
      (bool ok, bytes result) = msg.sender.call{value: remainingValue}(empty);
      if (result.length != 0) {
        require(result.length <= 18446744073709551615);
        var allocation = _allocate(32 + (result.length + 31) / 32 * 32);
      }
      require(ok);
    }
  }

  function ECDSA_toTypedDataHash(bytes32 domainSeparator, bytes32 structHash) internal returns (bytes32) {
    var allocation = _allocate(128);
    return keccak256(abi.encodePacked(bytes2(bytes2(0x1901)), bytes32(domainSeparator), bytes32(structHash)));
  }

  function ECDSA_tryRecover(bytes32 hash, uint8 v, bytes32 r, bytes32 s) internal returns (address, uint8) {
    if (uint256(s) > 57896044618658097711785492504343953926418782139537452191302581570759080747168) {
      return (address(0), 3);
    }
    address precompile = address(1);
    bytes payload = abi.encodePacked(bytes32(hash), uint256(v), bytes32(r), bytes32(s));
    (bool ok, bytes result) = precompile.staticcall(payload);
    require(ok);
    address signer = address(0);
    if (result.length >= 32) {
      signer = abi.decode(result, (address));
    }
    if (signer == address(0)) {
      return (address(0), 1);
    }
    return (signer, 0);
  }

  function ECDSA__throwError(uint8 error) internal {
    require(error < 5);
    if (error == 0) {
      return;
    } else {
      if (error == 1) {
        require(false);
      } else {
        if (error == 2) {
          require(false);
        } else {
          require(error != 3);
        }
      }
    }
  }

  function getAttestTypeHash() external returns (bytes32) {
    bytes __calldata = msg.data;
    require(uint256(__calldata.length - 4) < 57896044618658097711785492504343953926634992332820282019728792003956564819968);
    return bytes32(0xdbfdf8dc2b135c26253e00d5b6cbe6f20457e003fd526d97cea183883570de61);
  }

  function multiRevokeOffchain(bytes32[] calldata data) external returns (uint64) {
    bytes __calldata = msg.data;
    require(uint256(__calldata.length - 4) < 57896044618658097711785492504343953926634992332820282019728792003956564819968);
    var time = _time();
    uint256 length = data.length;
    uint256 i = 0;
    while (i < length) {
      var __c1 = _revokeOffchain(msg.sender, data[i], time);
      i = uint256(i + 1);
    }
    return time;
  }

  function getNonce(address account) external returns (uint256) {
    bytes __calldata = msg.data;
    require(uint256(__calldata.length - 4) < 57896044618658097711785492504343953926634992332820282019728792003956564819968);
    return _nonces[account];
  }

  function multiAttest(MultiAttestationRequest[] calldata multiRequests) external payable returns (bytes32[]) {
    bytes __calldata = msg.data;
    require(uint256(__calldata.length - 4) < 57896044618658097711785492504343953926634992332820282019728792003956564819968);
    require(multiRequests.length <= 18446744073709551615);
    var allocation = _allocate(32 + multiRequests.length * 32);
    bytes32[][] totalUids = new bytes32[][](multiRequests.length);
    uint256 totalUidsCount = 0;
    uint256 availableValue = msg.value;
    uint256 i = 0;
    while (i < multiRequests.length) {
      bool last = false;
      last = i == uint256(multiRequests.length - 1);
      MultiAttestationRequest multiRequest = multiRequests[i];
      ${checkedCalldata (.var "multiRequest")}
      var allocation = _copyAttestationArray(multiRequest.1);
      var res = _attest(multiRequest.0, multiRequest.1, msg.sender, availableValue, last);
      availableValue = ((availableValue - res.usedValue) as uint256);
      totalUids[i] = res.uids;
      totalUidsCount = uint256(totalUidsCount + res.uids.length);
      i = uint256(i + 1);
    }
    var __c1 = _mergeUIDs(totalUids, totalUidsCount);
    return __c1;
  }

  function revoke(RevocationRequest calldata request) external payable {
    bytes __calldata = msg.data;
    require(uint256(__calldata.length - 4) < 57896044618658097711785492504343953926634992332820282019728792003956564819968);
    var allocation = _allocate(192);
    RevocationRequestData[] requests = new RevocationRequestData[](1);
    requests[0] = request.1;
    var __c0 = _revoke(request.0, requests, msg.sender, msg.value, true);
  }

  function multiRevoke(MultiRevocationRequest[] calldata multiRequests) external payable {
    bytes __calldata = msg.data;
    require(uint256(__calldata.length - 4) < 57896044618658097711785492504343953926634992332820282019728792003956564819968);
    uint256 availableValue = msg.value;
    uint256 i = 0;
    while (i < multiRequests.length) {
      bool last = false;
      last = i == uint256(multiRequests.length - 1);
      MultiRevocationRequest multiRequest = multiRequests[i];
      ${checkedCalldata (.var "multiRequest")}
      RevocationRequestData[] data = multiRequest.1;
      require(data.length <= 18446744073709551615);
      var allocation = _allocate(32 + data.length * 96);
      var __c0 = _revoke(multiRequest.0, multiRequest.1, msg.sender, availableValue, last);
      availableValue = ((availableValue - __c0) as uint256);
      i = uint256(i + 1);
    }
  }

  function timestamp(bytes32 data) external returns (uint64) {
    bytes __calldata = msg.data;
    require(uint256(__calldata.length - 4) < 57896044618658097711785492504343953926634992332820282019728792003956564819968);
    var time = _time();
    var __c1 = _timestamp(data, time);
    return time;
  }

  function multiAttestByDelegation(MultiDelegatedAttestationRequest[] calldata multiDelegatedRequests) external payable returns (bytes32[]) {
    bytes __calldata = msg.data;
    require(uint256(__calldata.length - 4) < 57896044618658097711785492504343953926634992332820282019728792003956564819968);
    require(multiDelegatedRequests.length <= 18446744073709551615);
    var allocation = _allocate(32 + multiDelegatedRequests.length * 32);
    bytes32[][] totalUids = new bytes32[][](multiDelegatedRequests.length);
    uint256 totalUidsCount = 0;
    uint256 availableValue = msg.value;
    uint256 i = 0;
    while (i < multiDelegatedRequests.length) {
      bool last = false;
      last = i == uint256(multiDelegatedRequests.length - 1);
      MultiDelegatedAttestationRequest multiDelegatedRequest = multiDelegatedRequests[i];
      ${checkedCalldata (.var "multiDelegatedRequest")}
      AttestationRequestData[] data = multiDelegatedRequest.1;
      ${checkedCalldata (.var "data")}
      require(data.length != 0);
      EIP712Signature[] signatures = multiDelegatedRequest.2;
      ${checkedCalldata (.var "signatures")}
      require(data.length == signatures.length);
      uint256 j = 0;
      while (j < data.length) {
        AttestationRequestData datum = data[j];
        EIP712Signature signature = signatures[j];
        address attester = multiDelegatedRequest.3;
        ${checkedCalldata (.var "datum")}
        ${checkedCalldata (.var "attester")}
        ${checkedCalldata (.var "signature")}
        var allocation = _allocate(128);
        var allocation = _copyAttestationData(datum);
        var allocation = _allocate(96);
        var __c0 = _verifyAttest(DelegatedAttestationRequest({schema: multiDelegatedRequest.0, data: datum, signature: signature, attester: attester}));
        j = uint256(j + 1);
      }
      var __copyCheck = _checkAttestationArrayCopy(i, data.length);
      var allocation = _copyAttestationArray(data);
      var res = _attest(multiDelegatedRequest.0, data, multiDelegatedRequest.3, availableValue, last);
      availableValue = ((availableValue - res.usedValue) as uint256);
      totalUids[i] = res.uids;
      totalUidsCount = uint256(totalUidsCount + res.uids.length);
      i = uint256(i + 1);
    }
    var __c2 = _mergeUIDs(totalUids, totalUidsCount);
    return __c2;
  }

  function getAttestation(bytes32 uid) external returns ((bytes32, bytes32, uint64, uint64, uint64, bytes32, address, address, bool, bytes)) {
    bytes __calldata = msg.data;
    require(uint256(__calldata.length - 4) < 57896044618658097711785492504343953926634992332820282019728792003956564819968);
    var allocation = _allocate(320);
    var attestation = _copyStoredAttestation(uid);
    return tuple(attestation.uid, attestation.schema, attestation.time, attestation.expirationTime, attestation.revocationTime, attestation.refUID, attestation.recipient, attestation.attester, attestation.revocable, attestation.data);
  }

  function getRevokeOffchain(address revoker, bytes32 data) external returns (uint64) {
    bytes __calldata = msg.data;
    require(uint256(__calldata.length - 4) < 57896044618658097711785492504343953926634992332820282019728792003956564819968);
    return _revocationsOffchain[revoker][data];
  }

  function getRevokeTypeHash() external returns (bytes32) {
    bytes __calldata = msg.data;
    require(uint256(__calldata.length - 4) < 57896044618658097711785492504343953926634992332820282019728792003956564819968);
    return bytes32(0xa98d02348410c9c76735e0d0bb1396f4015ac2bb9615f9c2611d19d7a8a99650);
  }

  function revokeOffchain(bytes32 data) external returns (uint64) {
    bytes __calldata = msg.data;
    require(uint256(__calldata.length - 4) < 57896044618658097711785492504343953926634992332820282019728792003956564819968);
    var time = _time();
    var __c1 = _revokeOffchain(msg.sender, data, time);
    return time;
  }

  function getTimestamp(bytes32 data) external returns (uint64) {
    bytes __calldata = msg.data;
    require(uint256(__calldata.length - 4) < 57896044618658097711785492504343953926634992332820282019728792003956564819968);
    return _timestamps[data];
  }

  function attestByDelegation(DelegatedAttestationRequest calldata delegatedRequest) external payable returns (bytes32) {
    bytes __calldata = msg.data;
    require(uint256(__calldata.length - 4) < 57896044618658097711785492504343953926634992332820282019728792003956564819968);
    var allocation = _allocate(128);
    var allocation = _copyAttestationData(delegatedRequest.1);
    var allocation = _allocate(96);
    var delegatedRequest = DelegatedAttestationRequest({schema: delegatedRequest.0, data: delegatedRequest.1, signature: delegatedRequest.2, attester: delegatedRequest.3});
    var __c0 = _verifyAttest(delegatedRequest);
    var allocation = _allocate(256);
    var allocation = _copyAttestationData(delegatedRequest.data);
    AttestationRequestData[] data = new AttestationRequestData[](1);
    data[0] = delegatedRequest.data;
    var __c1 = _attest(delegatedRequest.schema, data, delegatedRequest.attester, msg.value, true);
    return __c1.uids[0];
  }

  function isAttestationValid(bytes32 uid) external returns (bool) {
    bytes __calldata = msg.data;
    require(uint256(__calldata.length - 4) < 57896044618658097711785492504343953926634992332820282019728792003956564819968);
    return _db[uid].uid != bytes32(0);
  }

  function multiRevokeByDelegation(MultiDelegatedRevocationRequest[] calldata multiDelegatedRequests) external payable {
    bytes __calldata = msg.data;
    require(uint256(__calldata.length - 4) < 57896044618658097711785492504343953926634992332820282019728792003956564819968);
    uint256 availableValue = msg.value;
    uint256 i = 0;
    while (i < multiDelegatedRequests.length) {
      bool last = false;
      last = i == uint256(multiDelegatedRequests.length - 1);
      MultiDelegatedRevocationRequest memory multiDelegatedRequest = multiDelegatedRequests[i];
      ${checkedCalldata (.var "multiDelegatedRequest")}
      RevocationRequestData[] memory data = multiDelegatedRequest.1;
      EIP712Signature[] signatures = multiDelegatedRequest.2;
      var allocation = _allocate(128);
      require(data.length <= 18446744073709551615);
      var allocation = _allocate(32 + data.length * 96);
      require(signatures.length <= 18446744073709551615);
      var allocation = _allocate(32 + signatures.length * 128);
      require(!(((data.length == 0) || (data.length != signatures.length))));
      uint256 j = 0;
      while (j < data.length) {
        var allocation = _allocate(128);
        var __c0 = _verifyRevoke(DelegatedRevocationRequest({schema: multiDelegatedRequest.0, data: data[j], signature: signatures[j], revoker: multiDelegatedRequest.3}));
        j = uint256(j + 1);
      }
      var __c1 = _revoke(multiDelegatedRequest.0, data, multiDelegatedRequest.3, availableValue, last);
      availableValue = ((availableValue - __c1) as uint256);
      i = uint256(i + 1);
    }
  }

  function revokeByDelegation(DelegatedRevocationRequest calldata delegatedRequest) external payable {
    bytes __calldata = msg.data;
    require(uint256(__calldata.length - 4) < 57896044618658097711785492504343953926634992332820282019728792003956564819968);
    var allocation = _allocate(288);
    var delegatedRequest = DelegatedRevocationRequest({schema: delegatedRequest.0, data: delegatedRequest.1, signature: delegatedRequest.2, revoker: delegatedRequest.3});
    var __c0 = _verifyRevoke(delegatedRequest);
    var allocation = _allocate(192);
    RevocationRequestData[] data = new RevocationRequestData[](1);
    data[0] = delegatedRequest.data;
    var __c1 = _revoke(delegatedRequest.schema, data, delegatedRequest.revoker, msg.value, true);
  }

  function multiTimestamp(bytes32[] calldata data) external returns (uint64) {
    bytes __calldata = msg.data;
    require(uint256(__calldata.length - 4) < 57896044618658097711785492504343953926634992332820282019728792003956564819968);
    var time = _time();
    uint256 length = data.length;
    uint256 i = 0;
    while (i < length) {
      var __c1 = _timestamp(data[i], time);
      i = uint256(i + 1);
    }
    return time;
  }

  function getDomainSeparator() external returns (bytes32) {
    bytes __calldata = msg.data;
    require(uint256(__calldata.length - 4) < 57896044618658097711785492504343953926634992332820282019728792003956564819968);
    var __c0 = _domainSeparatorV4();
    return __c0;
  }

  function getSchemaRegistry() external returns (address) {
    bytes __calldata = msg.data;
    require(uint256(__calldata.length - 4) < 57896044618658097711785492504343953926634992332820282019728792003956564819968);
    return _schemaRegistry;
  }

  function attest(AttestationRequest calldata request) external payable returns (bytes32) {
    bytes __calldata = msg.data;
    require(uint256(__calldata.length - 4) < 57896044618658097711785492504343953926634992332820282019728792003956564819968);
    var allocation = _allocate(256);
    var allocation = _copyAttestationData(request.1);
    AttestationRequestData[] requests = new AttestationRequestData[](1);
    requests[0] = request.1;
    var __c0 = _attest(request.0, requests, msg.sender, msg.value, true);
    return __c0.uids[0];
  }

  function VERSION() external returns (string) {
    bytes __calldata = msg.data;
    require(uint256(__calldata.length - 4) < 57896044618658097711785492504343953926634992332820282019728792003956564819968);
    var allocation = _allocate(64);
    return "0.26";
  }

}

/-- EAS with its compiler allocation guards, using only existing Solm statements. -/
def contractSyntax : ContractDecl := withAllocator contractBody

/-- Copy boundaries in the pinned 0.8.32 runtime. The incoming edge to a copied value may
    still be a calldata reference: e.g. `multiRequest.data` is accessed with a signed tail
    offset, then its elements are eagerly decoded for `_attest`/`_revoke`. The whole delegated
    revocation request is copied instead. Unlisted parameters use eager decoding.
    See `EAS.optimized.yul` and `HANDOFF.md` for the audit evidence. -/
def abiDecodeMode : ABI.DecodeMode := .solc08Calldata [
  -- multiAttest / multiRevoke: array elements stay in calldata; each data field is copied.
  (0x44adc90e, [{ materialize := [[.element, .field 1]], deferErrors := [[.element]] }]),
  (0x4cb7e9e5, [{ materialize := [[.element, .field 1]], deferErrors := [[.element]] }]),
  -- Verification copies one datum/signature at a time; the full data copy follows the loop.
  (0x831e05a1, [{
    materialize := [[.element, .field 1, .element], [.element, .field 2, .element]]
    deferErrors := [[.element], [.element, .field 1], [.element, .field 2], [.element, .field 3],
      [.element, .field 1, .element], [.element, .field 2, .element]] }]),
  -- multiRevokeByDelegation: the entire request is copied before accessing its fields.
  (0xe45d03f9, [{ materialize := [[.element]], deferErrors := [[.element]] }]),
  -- attest: the request's data tail is accessed directly, then the data struct is copied.
  (0xf17325e7, [{ materialize := [[.field 1]] }])
]

end Benchmarks.EAS.EAS.Syntax
