/// @use-src 9:"@openzeppelin/contracts/utils/cryptography/EIP712.sol", 11:"contracts/EAS.sol", 12:"contracts/EIP712Verifier.sol", 13:"contracts/IEAS.sol"
object "EAS_4789" {
    code {
        {
            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
            let _1 := memoryguard(0x0160)
            mstore(64, _1)
            if callvalue() { revert(0, 0) }
            let programSize := datasize("EAS_4789")
            let argSize := sub(codesize(), programSize)
            finalize_allocation(_1, argSize)
            codecopy(_1, programSize, argSize)
            if slt(sub(add(_1, argSize), _1), 32)
            {
                revert(/** @src -1:-1:-1 */ 0, 0)
            }
            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
            let value := mload(_1)
            let _2 := and(value, sub(shl(160, 1), 1))
            if iszero(eq(value, _2))
            {
                revert(/** @src -1:-1:-1 */ 0, 0)
            }
            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
            let memPtr := /** @src -1:-1:-1 */ 0
            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
            let size := /** @src -1:-1:-1 */ 0
            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
            size := /** @src -1:-1:-1 */ 0
            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
            let memPtr_1 := mload(64)
            finalize_allocation(memPtr_1, 64)
            memPtr := memPtr_1
            mstore(memPtr_1, 4)
            let _3 := add(memPtr_1, 32)
            mstore(_3, "0.26")
            let memPtr_2 := /** @src -1:-1:-1 */ 0
            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
            let size_1 := /** @src -1:-1:-1 */ 0
            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
            size_1 := /** @src -1:-1:-1 */ 0
            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
            let memPtr_3 := mload(64)
            finalize_allocation(memPtr_3, 64)
            memPtr_2 := memPtr_3
            mstore(memPtr_3, 3)
            let _4 := add(memPtr_3, 32)
            mstore(_4, "EAS")
            /// @src 9:2550:2572  "keccak256(bytes(name))"
            let expr := keccak256(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _4, mload(/** @src 9:2550:2572  "keccak256(bytes(name))" */ memPtr_3))
            /// @src 9:2606:2631  "keccak256(bytes(version))"
            let expr_1 := keccak256(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _3, mload(/** @src 9:2606:2631  "keccak256(bytes(version))" */ memPtr_1))
            /// @src 9:2787:2812  "_HASHED_NAME = hashedName"
            mstore(224, expr)
            /// @src 9:2822:2853  "_HASHED_VERSION = hashedVersion"
            mstore(256, expr_1)
            /// @src 9:2863:2895  "_CACHED_CHAIN_ID = block.chainid"
            mstore(160, /** @src 9:2882:2895  "block.chainid" */ chainid())
            /// @src 9:3642:3715  "abi.encode(typeHash, nameHash, versionHash, block.chainid, address(this))"
            let expr_mpos := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(64)
            /// @src 9:3642:3715  "abi.encode(typeHash, nameHash, versionHash, block.chainid, address(this))"
            let _5 := add(expr_mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 32)
            mstore(_5, /** @src 9:2660:2777  "keccak256(..." */ 0x8b73c3c69bb8fe3d512ecc4cf759cc79239f7b179b0ffacaa9a75d522b39400f)
            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
            mstore(add(/** @src 9:3642:3715  "abi.encode(typeHash, nameHash, versionHash, block.chainid, address(this))" */ expr_mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 64), expr)
            mstore(add(/** @src 9:3642:3715  "abi.encode(typeHash, nameHash, versionHash, block.chainid, address(this))" */ expr_mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 96), expr_1)
            mstore(add(/** @src 9:3642:3715  "abi.encode(typeHash, nameHash, versionHash, block.chainid, address(this))" */ expr_mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 128), /** @src 9:2882:2895  "block.chainid" */ chainid())
            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
            mstore(add(/** @src 9:3642:3715  "abi.encode(typeHash, nameHash, versionHash, block.chainid, address(this))" */ expr_mpos, /** @src 9:2863:2895  "_CACHED_CHAIN_ID = block.chainid" */ 160), /** @src 9:3709:3713  "this" */ address())
            /// @src 9:3642:3715  "abi.encode(typeHash, nameHash, versionHash, block.chainid, address(this))"
            mstore(expr_mpos, /** @src 9:2863:2895  "_CACHED_CHAIN_ID = block.chainid" */ 160)
            /// @src 9:3642:3715  "abi.encode(typeHash, nameHash, versionHash, block.chainid, address(this))"
            finalize_allocation(expr_mpos, 192)
            /// @src 9:2905:2990  "_CACHED_DOMAIN_SEPARATOR = _buildDomainSeparator(typeHash, hashedName, hashedVersion)"
            mstore(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 128, /** @src 9:3632:3716  "keccak256(abi.encode(typeHash, nameHash, versionHash, block.chainid, address(this)))" */ keccak256(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _5, mload(/** @src 9:3632:3716  "keccak256(abi.encode(typeHash, nameHash, versionHash, block.chainid, address(this)))" */ expr_mpos)))
            /// @src 9:3000:3028  "_CACHED_THIS = address(this)"
            mstore(/** @src 9:3642:3715  "abi.encode(typeHash, nameHash, versionHash, block.chainid, address(this))" */ 192, /** @src 9:3709:3713  "this" */ address())
            /// @src 9:3038:3059  "_TYPE_HASH = typeHash"
            mstore(288, /** @src 9:2660:2777  "keccak256(..." */ 0x8b73c3c69bb8fe3d512ecc4cf759cc79239f7b179b0ffacaa9a75d522b39400f)
            /// @src 11:2525:2611  "if (address(registry) == address(0)) {..."
            if /** @src 11:2529:2560  "address(registry) == address(0)" */ iszero(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _2)
            /// @src 11:2525:2611  "if (address(registry) == address(0)) {..."
            {
                /// @src 11:2583:2600  "InvalidRegistry()"
                mstore(/** @src -1:-1:-1 */ 0, /** @src 11:2583:2600  "InvalidRegistry()" */ shl(224, 0x11a1e697))
                revert(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 4)
            }
            /// @src 11:2621:2647  "_schemaRegistry = registry"
            mstore(320, value)
            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
            let _6 := mload(64)
            let _7 := datasize("EAS_4789_deployed")
            codecopy(_6, dataoffset("EAS_4789_deployed"), _7)
            setimmutable(_6, "1900", mload(128))
            setimmutable(_6, "1902", mload(/** @src 9:2863:2895  "_CACHED_CHAIN_ID = block.chainid" */ 160))
            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
            setimmutable(_6, "1904", mload(/** @src 9:3642:3715  "abi.encode(typeHash, nameHash, versionHash, block.chainid, address(this))" */ 192))
            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
            setimmutable(_6, "1906", mload(/** @src 9:2787:2812  "_HASHED_NAME = hashedName" */ 224))
            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
            setimmutable(_6, "1908", mload(/** @src 9:2822:2853  "_HASHED_VERSION = hashedVersion" */ 256))
            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
            setimmutable(_6, "1910", mload(/** @src 9:3038:3059  "_TYPE_HASH = typeHash" */ 288))
            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
            setimmutable(_6, "3001", mload(/** @src 11:2621:2647  "_schemaRegistry = registry" */ 320))
            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
            return(_6, _7)
        }
        function finalize_allocation(memPtr, size)
        {
            let newFreePtr := add(memPtr, and(add(size, 31), not(31)))
            if or(gt(newFreePtr, sub(shl(64, 1), 1)), lt(newFreePtr, memPtr))
            {
                mstore(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ shl(224, 0x4e487b71))
                mstore(4, 0x41)
                revert(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0x24)
            }
            mstore(64, newFreePtr)
        }
    }
    /// @use-src 5:"@openzeppelin/contracts/utils/Address.sol", 8:"@openzeppelin/contracts/utils/cryptography/ECDSA.sol", 9:"@openzeppelin/contracts/utils/cryptography/EIP712.sol", 11:"contracts/EAS.sol", 12:"contracts/EIP712Verifier.sol", 16:"contracts/Types.sol"
    object "EAS_4789_deployed" {
        code {
            {
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                let _1 := memoryguard(0xe0)
                mstore(64, _1)
                if iszero(lt(calldatasize(), 4))
                {
                    switch shr(224, calldataload(0))
                    case 0x12b11a17 {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc), 0) { revert(0, 0) }
                        mstore(_1, /** @src 12:921:987  "0xdbfdf8dc2b135c26253e00d5b6cbe6f20457e003fd526d97cea183883570de61" */ 0xdbfdf8dc2b135c26253e00d5b6cbe6f20457e003fd526d97cea183883570de61)
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        return(_1, 32)
                    }
                    case 0x13893f61 {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc), 32) { revert(0, 0) }
                        let offset := calldataload(4)
                        if gt(offset, 0xffffffffffffffff) { revert(0, 0) }
                        let value0, value1 := abi_decode_array_bytes32_dyn_calldata(add(4, offset), calldatasize())
                        let cleaned := and(/** @src 11:29893:29908  "block.timestamp" */ timestamp(), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffff)
                        /// @src 11:14409:14422  "uint256 i = 0"
                        let var_i := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0
                        /// @src 11:14404:14565  "for (uint256 i = 0; i < length; ) {..."
                        for { }
                        /** @src 11:14424:14434  "i < length" */ lt(var_i, value1)
                        /// @src 11:14409:14422  "uint256 i = 0"
                        { }
                        {
                            /// @src 11:14489:14493  "time"
                            fun_revokeOffchain(/** @src 11:14468:14478  "msg.sender" */ caller(), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ calldataload(/** @src 11:14480:14487  "data[i]" */ calldata_array_index_access_bytes32_dyn_calldata(value0, value1, var_i)), /** @src 11:14489:14493  "time" */ cleaned)
                            /// @src 11:14537:14540  "++i"
                            var_i := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ add(/** @src 11:14537:14540  "++i" */ var_i, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 1)
                        }
                        let memPos := mload(64)
                        mstore(memPos, cleaned)
                        return(memPos, 32)
                    }
                    case 0x2d0335ab {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc), 32) { revert(0, 0) }
                        mstore(0, and(abi_decode_address_16795(), 0xffffffffffffffffffffffffffffffffffffffff))
                        mstore(32, 0)
                        let _2 := sload(keccak256(0, 64))
                        let memPos_1 := mload(64)
                        mstore(memPos_1, _2)
                        return(memPos_1, 32)
                    }
                    case 0x44adc90e {
                        if slt(add(calldatasize(), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc), 32) { revert(0, 0) }
                        let offset_1 := calldataload(4)
                        if gt(offset_1, 0xffffffffffffffff) { revert(0, 0) }
                        let value0_1, value1_1 := abi_decode_array_bytes32_dyn_calldata(add(4, offset_1), calldatasize())
                        /// @src 11:3999:4036  "new bytes32[][](multiRequests.length)"
                        let expr_mpos := allocate_and_zero_memory_array_array_array_bytes32_dyn_dyn(value1_1)
                        /// @src 11:4046:4072  "uint256 totalUidsCount = 0"
                        let var_totalUidsCount := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0
                        /// @src 11:4486:4517  "uint availableValue = msg.value"
                        let var_availableValue := /** @src 11:4508:4517  "msg.value" */ callvalue()
                        /// @src 11:4533:4546  "uint256 i = 0"
                        let var_i_1 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0
                        /// @src 11:4926:4955  "i == multiRequests.length - 1"
                        let _3 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ add(/** @src 11:4931:4955  "multiRequests.length - 1" */ value1_1, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
                        /// @src 11:4528:5735  "for (uint256 i = 0; i < multiRequests.length; ) {..."
                        for { }
                        /** @src 11:4548:4572  "i < multiRequests.length" */ lt(var_i_1, value1_1)
                        /// @src 11:4533:4546  "uint256 i = 0"
                        { }
                        {
                            /// @src 11:5090:5106  "multiRequests[i]"
                            let expr_offset := calldata_array_index_access_struct_MultiAttestationRequest_calldata_dyn_calldata(value0_1, value1_1, var_i_1)
                            /// @src 11:5214:5231  "multiRequest.data"
                            let expr_offset_1, expr_length := access_calldata_tail_array_struct_AttestationRequestData_calldata_dyn_calldata(expr_offset, add(expr_offset, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 32))
                            /// @src 11:5152:5327  "_attest(..."
                            let expr_mpos_1 := fun_attest(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ calldataload(expr_offset), abi_decode_available_length_array_struct_AttestationRequestData_dyn(/** @src 11:5152:5327  "_attest(..." */ expr_offset_1, expr_length, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ calldatasize()), /** @src 11:5249:5259  "msg.sender" */ caller(), /** @src 11:5152:5327  "_attest(..." */ var_availableValue, /** @src 11:4926:4955  "i == multiRequests.length - 1" */ eq(var_i_1, _3))
                            /// @src 11:5454:5485  "availableValue -= res.usedValue"
                            var_availableValue := checked_sub_uint256(var_availableValue, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 11:5472:5485  "res.usedValue" */ expr_mpos_1))
                            /// @src 11:5567:5575  "res.uids"
                            let _4 := add(expr_mpos_1, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 32)
                            /// @src 11:5552:5575  "totalUids[i] = res.uids"
                            mstore(memory_array_index_access_array_bytes32_dyn_dyn(expr_mpos, var_i_1), /** @src 11:5567:5575  "res.uids" */ mload(_4))
                            /// @src 11:5552:5575  "totalUids[i] = res.uids"
                            pop(memory_array_index_access_array_bytes32_dyn_dyn(expr_mpos, var_i_1))
                            /// @src 11:5617:5650  "totalUidsCount += res.uids.length"
                            var_totalUidsCount := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ add(var_totalUidsCount, mload(/** @src 11:5635:5643  "res.uids" */ mload(_4)))
                            /// @src 11:5707:5710  "++i"
                            var_i_1 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ add(/** @src 11:5707:5710  "++i" */ var_i_1, /** @src 11:4954:4955  "1" */ 0x01)
                        }
                        /// @src 11:5821:5865  "return _mergeUIDs(totalUids, totalUidsCount)"
                        let var_mpos := /** @src 11:5828:5865  "_mergeUIDs(totalUids, totalUidsCount)" */ fun_mergeUIDs(expr_mpos, var_totalUidsCount)
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        let memPos_2 := mload(64)
                        return(memPos_2, sub(abi_encode_array_bytes32_dyn(memPos_2, var_mpos), memPos_2))
                    }
                    case 0x46926267 {
                        let _5 := slt(add(calldatasize(), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc), 96)
                        if _5 { revert(0, 0) }
                        _5 := 0
                        /// @src 11:9310:9340  "new RevocationRequestData[](1)"
                        let expr_mpos_2 := allocate_and_zero_memory_array_array_struct_RevocationRequestData_dyn()
                        /// @src 11:9350:9376  "requests[0] = request.data"
                        mstore(memory_array_index_access_array_array_bytes32_dyn_dyn(expr_mpos_2), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ abi_decode_struct_RevocationRequestData(calldatasize()))
                        /// @src 11:9350:9376  "requests[0] = request.data"
                        pop(memory_array_index_access_array_array_bytes32_dyn_dyn(expr_mpos_2))
                        /// @src 11:9387:9449  "_revoke(request.schema, requests, msg.sender, msg.value, true)"
                        pop(fun_revoke(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ calldataload(4), /** @src 11:9387:9449  "_revoke(request.schema, requests, msg.sender, msg.value, true)" */ expr_mpos_2, /** @src 11:9421:9431  "msg.sender" */ caller(), /** @src 11:9433:9442  "msg.value" */ callvalue()))
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        return(0, 0)
                    }
                    case 0x4cb7e9e5 {
                        if slt(add(calldatasize(), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc), 32) { revert(0, 0) }
                        let offset_2 := calldataload(4)
                        if gt(offset_2, 0xffffffffffffffff) { revert(0, 0) }
                        let value0_2, value1_2 := abi_decode_array_bytes32_dyn_calldata(add(4, offset_2), calldatasize())
                        /// @src 11:10413:10444  "uint availableValue = msg.value"
                        let var_availableValue_1 := /** @src 11:10435:10444  "msg.value" */ callvalue()
                        /// @src 11:10460:10473  "uint256 i = 0"
                        let var_i_2 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0
                        let _6 := add(/** @src 11:10858:10882  "multiRequests.length - 1" */ value1_2, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
                        /// @src 11:10455:11271  "for (uint256 i = 0; i < multiRequests.length; ) {..."
                        for { }
                        /** @src 11:10475:10499  "i < multiRequests.length" */ lt(var_i_2, value1_2)
                        /// @src 11:10460:10473  "uint256 i = 0"
                        { }
                        {
                            /// @src 11:10958:10974  "multiRequests[i]"
                            let expr_offset_2 := calldata_array_index_access_struct_MultiAttestationRequest_calldata_dyn_calldata(value0_2, value1_2, var_i_2)
                            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                            let rel_offset_of_tail := calldataload(/** @src 11:11148:11165  "multiRequest.data" */ add(expr_offset_2, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 32))
                            if iszero(slt(rel_offset_of_tail, add(sub(calldatasize(), expr_offset_2), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe1))) { revert(0, 0) }
                            let addr := add(expr_offset_2, rel_offset_of_tail)
                            let length := calldataload(addr)
                            if gt(length, 0xffffffffffffffff) { revert(0, 0) }
                            let addr_1 := add(addr, 32)
                            if sgt(addr_1, sub(calldatasize(), shl(6, length))) { revert(0, 0) }
                            /// @src 11:11101:11200  "availableValue -= _revoke(multiRequest.schema, multiRequest.data, msg.sender, availableValue, last)"
                            var_availableValue_1 := checked_sub_uint256(var_availableValue_1, /** @src 11:11119:11200  "_revoke(multiRequest.schema, multiRequest.data, msg.sender, availableValue, last)" */ fun__revoke(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ calldataload(expr_offset_2), abi_decode_available_length_array_struct_RevocationRequestData_dyn(/** @src 11:11119:11200  "_revoke(multiRequest.schema, multiRequest.data, msg.sender, availableValue, last)" */ addr_1, length, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ calldatasize()), /** @src 11:11167:11177  "msg.sender" */ caller(), /** @src 11:11119:11200  "_revoke(multiRequest.schema, multiRequest.data, msg.sender, availableValue, last)" */ var_availableValue_1, /** @src 11:10853:10882  "i == multiRequests.length - 1" */ eq(var_i_2, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _6)))
                            /// @src 11:11243:11246  "++i"
                            var_i_2 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ add(/** @src 11:11243:11246  "++i" */ var_i_2, /** @src 11:10881:10882  "1" */ 0x01)
                        }
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        return(0, 0)
                    }
                    case 0x4d003070 {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc), 32) { revert(0, 0) }
                        let cleaned_1 := and(/** @src 11:29893:29908  "block.timestamp" */ timestamp(), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffff)
                        /// @src 11:13944:13948  "time"
                        fun_timestamp(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ calldataload(4), /** @src 11:13944:13948  "time" */ cleaned_1)
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        let memPos_3 := mload(64)
                        mstore(memPos_3, cleaned_1)
                        return(memPos_3, 32)
                    }
                    case 0x831e05a1 {
                        if slt(add(calldatasize(), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc), 32) { revert(0, 0) }
                        let offset_3 := calldataload(4)
                        if gt(offset_3, 0xffffffffffffffff) { revert(0, 0) }
                        let value0_3, value1_3 := abi_decode_array_bytes32_dyn_calldata(add(4, offset_3), calldatasize())
                        /// @src 11:6290:6336  "new bytes32[][](multiDelegatedRequests.length)"
                        let expr_mpos_3 := allocate_and_zero_memory_array_array_array_bytes32_dyn_dyn(value1_3)
                        /// @src 11:6346:6372  "uint256 totalUidsCount = 0"
                        let var_totalUidsCount_1 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0
                        /// @src 11:6786:6817  "uint availableValue = msg.value"
                        let var_availableValue_2 := /** @src 11:6808:6817  "msg.value" */ callvalue()
                        /// @src 11:6833:6846  "uint256 i = 0"
                        let var_i_3 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0
                        /// @src 11:7235:7273  "i == multiDelegatedRequests.length - 1"
                        let _7 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ add(/** @src 11:7240:7273  "multiDelegatedRequests.length - 1" */ value1_3, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
                        /// @src 11:6828:9000  "for (uint256 i = 0; i < multiDelegatedRequests.length; ) {..."
                        for { }
                        /** @src 11:6848:6881  "i < multiDelegatedRequests.length" */ lt(var_i_3, value1_3)
                        /// @src 11:6833:6846  "uint256 i = 0"
                        { }
                        {
                            /// @src 11:7368:7393  "multiDelegatedRequests[i]"
                            let expr_offset_3 := calldata_array_index_access_struct_MultiDelegatedAttestationRequest_calldata_dyn_calldata(value0_3, value1_3, var_i_3)
                            /// @src 11:7448:7474  "multiDelegatedRequest.data"
                            let expr_offset_4, expr_length_1 := access_calldata_tail_array_struct_AttestationRequestData_calldata_dyn_calldata(expr_offset_3, add(expr_offset_3, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 32))
                            /// @src 11:7543:7617  "data.length == 0 || data.length != multiDelegatedRequest.signatures.length"
                            let expr := /** @src 11:7543:7559  "data.length == 0" */ iszero(expr_length_1)
                            /// @src 11:7543:7617  "data.length == 0 || data.length != multiDelegatedRequest.signatures.length"
                            if iszero(expr)
                            {
                                /// @src 11:7578:7610  "multiDelegatedRequest.signatures"
                                let expr_offset_5, expr_length_2 := access_calldata_tail_array_struct_EIP712Signature_calldata_dyn_calldata(expr_offset_3, add(expr_offset_3, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 64))
                                /// @src 11:7543:7617  "data.length == 0 || data.length != multiDelegatedRequest.signatures.length"
                                expr := /** @src 11:7563:7617  "data.length != multiDelegatedRequest.signatures.length" */ iszero(eq(expr_length_1, /** @src 11:7578:7617  "multiDelegatedRequest.signatures.length" */ expr_length_2))
                            }
                            /// @src 11:7539:7674  "if (data.length == 0 || data.length != multiDelegatedRequest.signatures.length) {..."
                            if expr
                            {
                                /// @src 11:7644:7659  "InvalidLength()"
                                mstore(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0, /** @src 11:7644:7659  "InvalidLength()" */ 0x947d5a8400000000000000000000000000000000000000000000000000000000)
                                revert(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0, 4)
                            }
                            /// @src 11:7815:7828  "uint256 j = 0"
                            let var_j := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0
                            /// @src 11:8068:8100  "multiDelegatedRequest.signatures"
                            let _8 := add(expr_offset_3, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 64)
                            /// @src 11:8139:8169  "multiDelegatedRequest.attester"
                            let _9 := add(expr_offset_3, 96)
                            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                            let value := calldataload(expr_offset_3)
                            /// @src 11:7810:8297  "for (uint256 j = 0; j < data.length; ) {..."
                            for { }
                            /** @src 11:7272:7273  "1" */ 0x01
                            /// @src 11:7815:7828  "uint256 j = 0"
                            { }
                            {
                                /// @src 11:7830:7845  "j < data.length"
                                let _10 := iszero(lt(var_j, expr_length_1))
                                if _10 { break }
                                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                                _10 := 0
                                let addr_2 := access_calldata_tail_struct_AttestationRequestData_calldata(expr_offset_4, add(expr_offset_4, shl(5, var_j)))
                                /// @src 11:8068:8100  "multiDelegatedRequest.signatures"
                                let expr_offset_6, expr_length_3 := access_calldata_tail_array_struct_EIP712Signature_calldata_dyn_calldata(expr_offset_3, _8)
                                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                                if iszero(lt(var_j, expr_length_3))
                                {
                                    mstore(_10, 35408467139433450592217433187231851964531694900788300625387963629091585785856)
                                    mstore(4, 0x32)
                                    revert(_10, 0x24)
                                }
                                /// @src 11:8139:8169  "multiDelegatedRequest.attester"
                                let expr_1 := read_from_calldatat_address(_9)
                                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                                let memPtr := mload(64)
                                finalize_allocation_16801(memPtr)
                                mstore(memPtr, value)
                                mstore(/** @src 11:7902:8192  "DelegatedAttestationRequest({..." */ add(memPtr, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 32), abi_decode_struct_AttestationRequestData(/** @src 11:7902:8192  "DelegatedAttestationRequest({..." */ addr_2, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ calldatasize()))
                                mstore(/** @src 11:7902:8192  "DelegatedAttestationRequest({..." */ add(memPtr, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 64), abi_decode_struct_EIP712Signature(add(expr_offset_6, mul(var_j, /** @src 11:8139:8169  "multiDelegatedRequest.attester" */ 96)), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ calldatasize()))
                                mstore(/** @src 11:7902:8192  "DelegatedAttestationRequest({..." */ add(memPtr, /** @src 11:8139:8169  "multiDelegatedRequest.attester" */ 96), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(expr_1, 0xffffffffffffffffffffffffffffffffffffffff))
                                /// @src 11:7902:8192  "DelegatedAttestationRequest({..."
                                fun_verifyAttest(memPtr)
                                /// @src 11:8261:8264  "++j"
                                var_j := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ add(/** @src 11:8261:8264  "++j" */ var_j, /** @src 11:7272:7273  "1" */ 0x01)
                            }
                            /// @src 11:8401:8592  "_attest(..."
                            let expr_mpos_4 := fun_attest(value, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ abi_decode_available_length_array_struct_AttestationRequestData_dyn(/** @src 11:8401:8592  "_attest(..." */ expr_offset_4, expr_length_1, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ calldatasize()), /** @src 11:8494:8524  "multiDelegatedRequest.attester" */ read_from_calldatat_address(_9), /** @src 11:8401:8592  "_attest(..." */ var_availableValue_2, /** @src 11:7235:7273  "i == multiDelegatedRequests.length - 1" */ eq(var_i_3, _7))
                            /// @src 11:8719:8750  "availableValue -= res.usedValue"
                            var_availableValue_2 := checked_sub_uint256(var_availableValue_2, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 11:8737:8750  "res.usedValue" */ expr_mpos_4))
                            /// @src 11:8832:8840  "res.uids"
                            let _11 := add(expr_mpos_4, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 32)
                            /// @src 11:8817:8840  "totalUids[i] = res.uids"
                            mstore(memory_array_index_access_array_bytes32_dyn_dyn(expr_mpos_3, var_i_3), /** @src 11:8832:8840  "res.uids" */ mload(_11))
                            /// @src 11:8817:8840  "totalUids[i] = res.uids"
                            pop(memory_array_index_access_array_bytes32_dyn_dyn(expr_mpos_3, var_i_3))
                            /// @src 11:8882:8915  "totalUidsCount += res.uids.length"
                            var_totalUidsCount_1 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ add(var_totalUidsCount_1, mload(/** @src 11:8900:8908  "res.uids" */ mload(_11)))
                            /// @src 11:8972:8975  "++i"
                            var_i_3 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ add(/** @src 11:8972:8975  "++i" */ var_i_3, /** @src 11:7272:7273  "1" */ 0x01)
                        }
                        /// @src 11:9086:9130  "return _mergeUIDs(totalUids, totalUidsCount)"
                        let var_mpos_1 := /** @src 11:9093:9130  "_mergeUIDs(totalUids, totalUidsCount)" */ fun_mergeUIDs(expr_mpos_3, var_totalUidsCount_1)
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        let memPos_4 := mload(64)
                        return(memPos_4, sub(abi_encode_array_bytes32_dyn(memPos_4, var_mpos_1), memPos_4))
                    }
                    case 0xa3112a64 {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc), 32) { revert(0, 0) }
                        pop(allocate_and_zero_memory_struct_struct_Attestation())
                        mstore(0, calldataload(4))
                        mstore(32, 1)
                        let converted := read_from_storage_reference_type_struct_Attestation(keccak256(0, 64))
                        let memPos_5 := mload(64)
                        mstore(memPos_5, 32)
                        return(memPos_5, sub(abi_encode_struct_Attestation(converted, add(memPos_5, 32)), memPos_5))
                    }
                    case 0xb469318d {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc), 64) { revert(0, 0) }
                        mstore(0, and(abi_decode_address_16795(), 0xffffffffffffffffffffffffffffffffffffffff))
                        mstore(32, /** @src 11:15587:15607  "_revocationsOffchain" */ 0x03)
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        let dataSlot := keccak256(0, 64)
                        mstore(0, calldataload(36))
                        mstore(32, dataSlot)
                        let cleaned_2 := and(sload(keccak256(0, 64)), 0xffffffffffffffff)
                        let memPos_6 := mload(64)
                        mstore(memPos_6, cleaned_2)
                        return(memPos_6, 32)
                    }
                    case 0xb83010d3 {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc), 0) { revert(0, 0) }
                        let memPos_7 := mload(64)
                        mstore(memPos_7, /** @src 12:1202:1268  "0xa98d02348410c9c76735e0d0bb1396f4015ac2bb9615f9c2611d19d7a8a99650" */ 0xa98d02348410c9c76735e0d0bb1396f4015ac2bb9615f9c2611d19d7a8a99650)
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        return(memPos_7, 32)
                    }
                    case 0xcf190f34 {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc), 32) { revert(0, 0) }
                        let cleaned_3 := and(/** @src 11:29893:29908  "block.timestamp" */ timestamp(), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffff)
                        /// @src 11:14164:14168  "time"
                        fun_revokeOffchain(/** @src 11:14146:14156  "msg.sender" */ caller(), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ calldataload(4), /** @src 11:14164:14168  "time" */ cleaned_3)
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        let memPos_8 := mload(64)
                        mstore(memPos_8, cleaned_3)
                        return(memPos_8, 32)
                    }
                    case 0xd45c4435 {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc), 32) { revert(0, 0) }
                        mstore(0, calldataload(4))
                        mstore(32, /** @src 11:15409:15420  "_timestamps" */ 0x02)
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        let cleaned_4 := and(sload(keccak256(0, 64)), 0xffffffffffffffff)
                        let memPos_9 := mload(64)
                        mstore(memPos_9, cleaned_4)
                        return(memPos_9, 32)
                    }
                    case 0xe13458fc {
                        if slt(add(calldatasize(), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc), 32) { revert(0, 0) }
                        let offset_4 := calldataload(4)
                        if gt(offset_4, 0xffffffffffffffff) { revert(0, 0) }
                        let _12 := add(4, offset_4)
                        let _13 := slt(add(sub(calldatasize(), offset_4), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc), 192)
                        if _13 { revert(0, 0) }
                        _13 := 0
                        let memPtr_1 := mload(64)
                        finalize_allocation_16801(memPtr_1)
                        let value_1 := calldataload(_12)
                        mstore(memPtr_1, value_1)
                        let _14 := add(offset_4, 36)
                        let offset_5 := calldataload(_14)
                        if gt(offset_5, 0xffffffffffffffff) { revert(0, 0) }
                        mstore(add(memPtr_1, 32), abi_decode_struct_AttestationRequestData(add(add(offset_4, offset_5), 4), calldatasize()))
                        mstore(add(memPtr_1, 64), abi_decode_struct_EIP712Signature(add(offset_4, 68), calldatasize()))
                        let _15 := add(offset_4, 164)
                        mstore(add(memPtr_1, 0x60), abi_decode_address(_15))
                        /// @src 11:3357:3388  "_verifyAttest(delegatedRequest)"
                        fun_verifyAttest(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ memPtr_1)
                        /// @src 11:3438:3469  "new AttestationRequestData[](1)"
                        let expr_mpos_5 := allocate_and_zero_memory_array_array_struct_AttestationRequestData_dyn()
                        /// @src 11:3479:3510  "data[0] = delegatedRequest.data"
                        mstore(memory_array_index_access_array_array_bytes32_dyn_dyn(expr_mpos_5), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ abi_decode_struct_AttestationRequestData(/** @src 11:3489:3510  "delegatedRequest.data" */ access_calldata_tail_struct_AttestationRequestData_calldata(_12, _14), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ calldatasize()))
                        /// @src 11:3479:3510  "data[0] = delegatedRequest.data"
                        pop(memory_array_index_access_array_array_bytes32_dyn_dyn(expr_mpos_5))
                        /// @src 11:3567:3592  "delegatedRequest.attester"
                        let expr_2 := read_from_calldatat_address(_15)
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        let _16 := mload(/** @src 11:3528:3618  "_attest(delegatedRequest.schema, data, delegatedRequest.attester, msg.value, true).uids[0]" */ memory_array_index_access_array_array_bytes32_dyn_dyn(/** @src 11:3528:3615  "_attest(delegatedRequest.schema, data, delegatedRequest.attester, msg.value, true).uids" */ mload(add(/** @src 11:3528:3610  "_attest(delegatedRequest.schema, data, delegatedRequest.attester, msg.value, true)" */ fun__attest(value_1, expr_mpos_5, expr_2, /** @src 11:3594:3603  "msg.value" */ callvalue()), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 32))))
                        let memPos_10 := mload(64)
                        mstore(memPos_10, _16)
                        return(memPos_10, 32)
                    }
                    case 0xe30bb563 {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc), 32) { revert(0, 0) }
                        let ret := fun_isAttestationValid(calldataload(4))
                        let memPos_11 := mload(64)
                        mstore(memPos_11, iszero(iszero(ret)))
                        return(memPos_11, 32)
                    }
                    case 0xe45d03f9 {
                        if slt(add(calldatasize(), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc), 32) { revert(0, 0) }
                        let offset_6 := calldataload(4)
                        if gt(offset_6, 0xffffffffffffffff) { revert(0, 0) }
                        let value0_4, value1_4 := abi_decode_array_bytes32_dyn_calldata(add(4, offset_6), calldatasize())
                        /// @src 11:11867:11898  "uint availableValue = msg.value"
                        let var_availableValue_3 := /** @src 11:11889:11898  "msg.value" */ callvalue()
                        /// @src 11:11914:11927  "uint256 i = 0"
                        let var_i_4 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0
                        let _17 := add(/** @src 11:12321:12354  "multiDelegatedRequests.length - 1" */ value1_4, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
                        /// @src 11:11909:13774  "for (uint256 i = 0; i < multiDelegatedRequests.length; ) {..."
                        for { }
                        /** @src 11:11929:11962  "i < multiDelegatedRequests.length" */ lt(var_i_4, value1_4)
                        /// @src 11:11914:11927  "uint256 i = 0"
                        { }
                        {
                            /// @src 11:12446:12471  "multiDelegatedRequests[i]"
                            let _18 := calldata_array_index_access_struct_MultiDelegatedAttestationRequest_calldata_dyn_calldata(value0_4, value1_4, var_i_4)
                            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                            if slt(sub(calldatasize(), _18), 0x80) { revert(0, 0) }
                            let memPtr_2 := mload(64)
                            finalize_allocation_16801(memPtr_2)
                            mstore(memPtr_2, calldataload(_18))
                            let offset_7 := calldataload(add(_18, 32))
                            if gt(offset_7, 0xffffffffffffffff) { revert(0, 0) }
                            let _19 := add(_18, offset_7)
                            if iszero(slt(add(_19, 0x1f), calldatasize())) { revert(0, 0) }
                            let array := abi_decode_available_length_array_struct_RevocationRequestData_dyn(add(_19, 32), calldataload(_19), calldatasize())
                            let _20 := add(memPtr_2, 32)
                            mstore(_20, array)
                            let offset_8 := calldataload(add(_18, 64))
                            if gt(offset_8, 0xffffffffffffffff) { revert(0, 0) }
                            let _21 := add(_18, offset_8)
                            if iszero(slt(add(_21, 0x1f), calldatasize())) { revert(0, 0) }
                            let length_1 := calldataload(_21)
                            let _22 := array_allocation_size_array_array_bytes32_dyn_dyn(length_1)
                            let memPtr_3 := mload(64)
                            finalize_allocation(memPtr_3, _22)
                            let dst := memPtr_3
                            mstore(memPtr_3, length_1)
                            dst := add(memPtr_3, 32)
                            let srcEnd := add(add(_21, mul(length_1, 0x60)), 32)
                            if gt(srcEnd, calldatasize()) { revert(0, 0) }
                            let src := add(_21, 32)
                            for { } lt(src, srcEnd) { src := add(src, 0x60) }
                            {
                                mstore(dst, abi_decode_struct_EIP712Signature(src, calldatasize()))
                                dst := add(dst, 32)
                            }
                            let _23 := add(memPtr_2, 64)
                            mstore(_23, memPtr_3)
                            let _24 := abi_decode_address(add(_18, 0x60))
                            let _25 := add(memPtr_2, 0x60)
                            mstore(_25, _24)
                            /// @src 11:12523:12549  "multiDelegatedRequest.data"
                            let _mpos := mload(_20)
                            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                            let _26 := mload(/** @src 11:12618:12629  "data.length" */ _mpos)
                            /// @src 11:12618:12692  "data.length == 0 || data.length != multiDelegatedRequest.signatures.length"
                            let expr_3 := /** @src 11:12618:12634  "data.length == 0" */ iszero(_26)
                            /// @src 11:12618:12692  "data.length == 0 || data.length != multiDelegatedRequest.signatures.length"
                            if iszero(expr_3)
                            {
                                expr_3 := /** @src 11:12638:12692  "data.length != multiDelegatedRequest.signatures.length" */ iszero(eq(_26, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(memPtr_3)))
                            }
                            /// @src 11:12614:12749  "if (data.length == 0 || data.length != multiDelegatedRequest.signatures.length) {..."
                            if expr_3
                            {
                                /// @src 11:12719:12734  "InvalidLength()"
                                mstore(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0, /** @src 11:12719:12734  "InvalidLength()" */ 0x947d5a8400000000000000000000000000000000000000000000000000000000)
                                revert(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0, 4)
                            }
                            /// @src 11:12890:12903  "uint256 j = 0"
                            let var_j_1 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0
                            /// @src 11:12885:13369  "for (uint256 j = 0; j < data.length; ) {..."
                            for { }
                            /** @src 11:12353:12354  "1" */ 0x01
                            /// @src 11:12890:12903  "uint256 j = 0"
                            { }
                            {
                                /// @src 11:12905:12920  "j < data.length"
                                if iszero(lt(var_j_1, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 11:12909:12920  "data.length" */ _mpos)))
                                /// @src 11:12905:12920  "j < data.length"
                                { break }
                                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                                let _27 := mload(/** @src 11:13038:13066  "multiDelegatedRequest.schema" */ memPtr_2)
                                /// @src 11:13098:13105  "data[j]"
                                let _mpos_1 := mload(memory_array_index_access_array_bytes32_dyn_dyn(_mpos, var_j_1))
                                /// @src 11:13142:13177  "multiDelegatedRequest.signatures[j]"
                                let _mpos_2 := mload(memory_array_index_access_array_bytes32_dyn_dyn(/** @src 11:13142:13174  "multiDelegatedRequest.signatures" */ mload(_23), /** @src 11:13142:13177  "multiDelegatedRequest.signatures[j]" */ var_j_1))
                                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                                let cleaned_5 := and(mload(/** @src 11:13212:13241  "multiDelegatedRequest.revoker" */ _25), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffff)
                                let memPtr_4 := mload(64)
                                finalize_allocation_16801(memPtr_4)
                                mstore(memPtr_4, _27)
                                mstore(/** @src 11:12977:13264  "DelegatedRevocationRequest({..." */ add(memPtr_4, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 32), _mpos_1)
                                mstore(/** @src 11:12977:13264  "DelegatedRevocationRequest({..." */ add(memPtr_4, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 64), _mpos_2)
                                mstore(/** @src 11:12977:13264  "DelegatedRevocationRequest({..." */ add(memPtr_4, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0x60), cleaned_5)
                                /// @src 11:12977:13264  "DelegatedRevocationRequest({..."
                                fun_verifyRevoke(memPtr_4)
                                /// @src 11:13333:13336  "++j"
                                var_j_1 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ add(/** @src 11:13333:13336  "++j" */ var_j_1, /** @src 11:12353:12354  "1" */ 0x01)
                            }
                            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                            let _28 := mload(/** @src 11:13538:13566  "multiDelegatedRequest.schema" */ memPtr_2)
                            /// @src 11:13495:13703  "availableValue -= _revoke(..."
                            var_availableValue_3 := checked_sub_uint256(var_availableValue_3, /** @src 11:13513:13703  "_revoke(..." */ fun__revoke(_28, _mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(mload(/** @src 11:13606:13635  "multiDelegatedRequest.revoker" */ _25), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffff), /** @src 11:13513:13703  "_revoke(..." */ var_availableValue_3, /** @src 11:12316:12354  "i == multiDelegatedRequests.length - 1" */ eq(var_i_4, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _17)))
                            /// @src 11:13746:13749  "++i"
                            var_i_4 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ add(/** @src 11:13746:13749  "++i" */ var_i_4, /** @src 11:12353:12354  "1" */ 0x01)
                        }
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        return(0, 0)
                    }
                    case 0xe57a6b1b {
                        let _29 := slt(add(calldatasize(), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc), 224)
                        if _29 { revert(0, 0) }
                        _29 := 0
                        _29 := 0
                        let memPtr_5 := mload(64)
                        finalize_allocation_16801(memPtr_5)
                        let value_2 := calldataload(4)
                        mstore(memPtr_5, value_2)
                        mstore(add(memPtr_5, 32), abi_decode_struct_RevocationRequestData(calldatasize()))
                        let value_3 := 0
                        if slt(add(calldatasize(), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9c), 96) { revert(0, 0) }
                        let memPtr_6 := mload(64)
                        finalize_allocation_16869(memPtr_6)
                        value_3 := memPtr_6
                        let value_4 := calldataload(100)
                        if iszero(eq(value_4, and(value_4, 0xff))) { revert(0, 0) }
                        mstore(memPtr_6, value_4)
                        mstore(add(memPtr_6, 32), calldataload(132))
                        mstore(add(memPtr_6, 64), calldataload(164))
                        mstore(add(memPtr_5, 64), memPtr_6)
                        let value_5 := 0
                        value_5 := calldataload(196)
                        let _30 := iszero(eq(value_5, and(value_5, 0xffffffffffffffffffffffffffffffffffffffff)))
                        if _30 { revert(0, 0) }
                        mstore(add(memPtr_5, 96), value_5)
                        /// @src 11:9617:9648  "_verifyRevoke(delegatedRequest)"
                        fun_verifyRevoke(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ memPtr_5)
                        /// @src 11:9697:9727  "new RevocationRequestData[](1)"
                        let expr_mpos_6 := allocate_and_zero_memory_array_array_struct_RevocationRequestData_dyn()
                        /// @src 11:9737:9768  "data[0] = delegatedRequest.data"
                        mstore(memory_array_index_access_array_array_bytes32_dyn_dyn(expr_mpos_6), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ abi_decode_struct_RevocationRequestData(calldatasize()))
                        /// @src 11:9737:9768  "data[0] = delegatedRequest.data"
                        pop(memory_array_index_access_array_array_bytes32_dyn_dyn(expr_mpos_6))
                        /// @src 11:9818:9842  "delegatedRequest.revoker"
                        let returnValue := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0
                        _30 := 0
                        returnValue := value_5
                        /// @src 11:9779:9860  "_revoke(delegatedRequest.schema, data, delegatedRequest.revoker, msg.value, true)"
                        pop(fun_revoke(value_2, expr_mpos_6, value_5, /** @src 11:9844:9853  "msg.value" */ callvalue()))
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        return(0, 0)
                    }
                    case 0xe71ff365 {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc), 32) { revert(0, 0) }
                        let offset_9 := calldataload(4)
                        if gt(offset_9, 0xffffffffffffffff) { revert(0, 0) }
                        let value0_5, value1_5 := abi_decode_array_bytes32_dyn_calldata(add(4, offset_9), calldatasize())
                        let cleaned_6 := and(/** @src 11:29893:29908  "block.timestamp" */ timestamp(), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffff)
                        /// @src 11:14799:14812  "uint256 i = 0"
                        let var_i_5 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0
                        /// @src 11:14794:14938  "for (uint256 i = 0; i < length; ) {..."
                        for { }
                        /** @src 11:14814:14824  "i < length" */ lt(var_i_5, value1_5)
                        /// @src 11:14799:14812  "uint256 i = 0"
                        { }
                        {
                            /// @src 11:14862:14866  "time"
                            fun_timestamp(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ calldataload(/** @src 11:14853:14860  "data[i]" */ calldata_array_index_access_bytes32_dyn_calldata(value0_5, value1_5, var_i_5)), /** @src 11:14862:14866  "time" */ cleaned_6)
                            /// @src 11:14910:14913  "++i"
                            var_i_5 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ add(/** @src 11:14910:14913  "++i" */ var_i_5, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 1)
                        }
                        let memPos_12 := mload(64)
                        mstore(memPos_12, cleaned_6)
                        return(memPos_12, 32)
                    }
                    case 0xed24911d {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc), 0) { revert(0, 0) }
                        let ret_1 := /** @src 12:1767:1787  "_domainSeparatorV4()" */ fun_domainSeparatorV4()
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        let memPos_13 := mload(64)
                        mstore(memPos_13, ret_1)
                        return(memPos_13, 32)
                    }
                    case 0xf10b5cc8 {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc), 0) { revert(0, 0) }
                        let memPos_14 := mload(64)
                        mstore(memPos_14, and(/** @src 11:2786:2801  "_schemaRegistry" */ loadimmutable("3001"), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                        return(memPos_14, 32)
                    }
                    case 0xf17325e7 {
                        if slt(add(calldatasize(), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc), 32) { revert(0, 0) }
                        let offset_10 := calldataload(4)
                        if gt(offset_10, 0xffffffffffffffff) { revert(0, 0) }
                        let _31 := add(4, offset_10)
                        if slt(add(sub(calldatasize(), offset_10), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc), 64) { revert(0, 0) }
                        /// @src 11:3001:3032  "new AttestationRequestData[](1)"
                        let expr_mpos_7 := allocate_and_zero_memory_array_array_struct_AttestationRequestData_dyn()
                        /// @src 11:3042:3068  "requests[0] = request.data"
                        mstore(memory_array_index_access_array_array_bytes32_dyn_dyn(expr_mpos_7), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ abi_decode_struct_AttestationRequestData(/** @src 11:3056:3068  "request.data" */ access_calldata_tail_struct_AttestationRequestData_calldata(_31, add(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ offset_10, /** @src 11:3056:3068  "request.data" */ 36)), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ calldatasize()))
                        /// @src 11:3042:3068  "requests[0] = request.data"
                        pop(memory_array_index_access_array_array_bytes32_dyn_dyn(expr_mpos_7))
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        let _32 := mload(/** @src 11:3086:3156  "_attest(request.schema, requests, msg.sender, msg.value, true).uids[0]" */ memory_array_index_access_array_array_bytes32_dyn_dyn(/** @src 11:3086:3153  "_attest(request.schema, requests, msg.sender, msg.value, true).uids" */ mload(add(/** @src 11:3086:3148  "_attest(request.schema, requests, msg.sender, msg.value, true)" */ fun__attest(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ calldataload(_31), /** @src 11:3086:3148  "_attest(request.schema, requests, msg.sender, msg.value, true)" */ expr_mpos_7, /** @src 11:3120:3130  "msg.sender" */ caller(), /** @src 11:3132:3141  "msg.value" */ callvalue()), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 32))))
                        let memPos_15 := mload(64)
                        mstore(memPos_15, _32)
                        return(memPos_15, 32)
                    }
                    case 0xffa1ad74 {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc), 0) { revert(0, 0) }
                        let size := 0
                        let _33 := size
                        _33 := size
                        size := 64
                        let memPtr_7 := mload(size)
                        finalize_allocation(memPtr_7, size)
                        mstore(memPtr_7, 4)
                        mstore(add(memPtr_7, 32), "0.26")
                        let memPos_16 := mload(size)
                        mstore(memPos_16, 32)
                        return(memPos_16, sub(abi_encode_bytes(memPtr_7, add(memPos_16, 32)), memPos_16))
                    }
                }
                revert(0, 0)
            }
            function abi_decode_array_bytes32_dyn_calldata(offset, end) -> arrayPos, length
            {
                if iszero(slt(add(offset, 0x1f), end)) { revert(0, 0) }
                length := calldataload(offset)
                if gt(length, 0xffffffffffffffff) { revert(0, 0) }
                arrayPos := add(offset, 0x20)
                if gt(add(add(offset, shl(5, length)), 0x20), end) { revert(0, 0) }
            }
            function abi_decode_address_16795() -> value
            {
                value := calldataload(4)
                if iszero(eq(value, and(value, 0xffffffffffffffffffffffffffffffffffffffff))) { revert(0, 0) }
            }
            function abi_decode_address(offset) -> value
            {
                value := calldataload(offset)
                if iszero(eq(value, and(value, 0xffffffffffffffffffffffffffffffffffffffff))) { revert(0, 0) }
            }
            function abi_encode_array_bytes32_dyn(headStart, value0) -> tail
            {
                let tail_1 := add(headStart, 32)
                mstore(headStart, 32)
                let pos := tail_1
                let length := mload(value0)
                mstore(tail_1, length)
                pos := add(headStart, 64)
                let srcPtr := add(value0, 32)
                let i := 0
                for { } lt(i, length) { i := add(i, 1) }
                {
                    mstore(pos, mload(srcPtr))
                    pos := add(pos, 32)
                    srcPtr := add(srcPtr, 32)
                }
                tail := pos
            }
            function copy_memory_to_memory_with_cleanup(src, dst, length)
            {
                let i := 0
                for { } lt(i, length) { i := add(i, 32) }
                {
                    mstore(add(dst, i), mload(add(src, i)))
                }
                mstore(add(dst, length), 0)
            }
            function abi_encode_bytes(value, pos) -> end
            {
                let length := mload(value)
                mstore(pos, length)
                copy_memory_to_memory_with_cleanup(add(value, 0x20), add(pos, 0x20), length)
                end := add(add(pos, and(add(length, 31), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0)), 0x20)
            }
            function abi_encode_struct_Attestation(value, pos) -> end
            {
                mstore(pos, mload(value))
                mstore(add(pos, 0x20), mload(add(value, 0x20)))
                mstore(add(pos, 0x40), and(mload(add(value, 0x40)), 0xffffffffffffffff))
                mstore(add(pos, 0x60), and(mload(add(value, 0x60)), 0xffffffffffffffff))
                mstore(add(pos, 0x80), and(mload(add(value, 0x80)), 0xffffffffffffffff))
                mstore(add(pos, 0xa0), mload(add(value, 0xa0)))
                mstore(add(pos, 0xc0), and(mload(add(value, 0xc0)), 0xffffffffffffffffffffffffffffffffffffffff))
                mstore(add(pos, 0xe0), and(mload(add(value, 0xe0)), 0xffffffffffffffffffffffffffffffffffffffff))
                mstore(add(pos, 0x0100), iszero(iszero(mload(add(value, 0x0100)))))
                let memberValue0 := mload(add(value, 0x0120))
                mstore(add(pos, 0x0120), 0x0140)
                end := abi_encode_bytes(memberValue0, add(pos, 0x0140))
            }
            function finalize_allocation_16801(memPtr)
            {
                let newFreePtr := add(memPtr, 128)
                if or(gt(newFreePtr, 0xffffffffffffffff), lt(newFreePtr, memPtr))
                {
                    mstore(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 35408467139433450592217433187231851964531694900788300625387963629091585785856)
                    mstore(4, 0x41)
                    revert(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0x24)
                }
                mstore(64, newFreePtr)
            }
            function finalize_allocation_16860(memPtr)
            {
                let newFreePtr := add(memPtr, 0xc0)
                if or(gt(newFreePtr, 0xffffffffffffffff), lt(newFreePtr, memPtr))
                {
                    mstore(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 35408467139433450592217433187231851964531694900788300625387963629091585785856)
                    mstore(4, 0x41)
                    revert(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0x24)
                }
                mstore(64, newFreePtr)
            }
            function finalize_allocation_16863(memPtr)
            {
                let newFreePtr := add(memPtr, 64)
                if or(gt(newFreePtr, 0xffffffffffffffff), lt(newFreePtr, memPtr))
                {
                    mstore(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 35408467139433450592217433187231851964531694900788300625387963629091585785856)
                    mstore(4, 0x41)
                    revert(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0x24)
                }
                mstore(64, newFreePtr)
            }
            function finalize_allocation_16869(memPtr)
            {
                let newFreePtr := add(memPtr, 0x60)
                if or(gt(newFreePtr, 0xffffffffffffffff), lt(newFreePtr, memPtr))
                {
                    mstore(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 35408467139433450592217433187231851964531694900788300625387963629091585785856)
                    mstore(4, 0x41)
                    revert(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0x24)
                }
                mstore(64, newFreePtr)
            }
            function finalize_allocation_16871(memPtr)
            {
                let newFreePtr := add(memPtr, 320)
                if or(gt(newFreePtr, 0xffffffffffffffff), lt(newFreePtr, memPtr))
                {
                    mstore(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 35408467139433450592217433187231851964531694900788300625387963629091585785856)
                    mstore(4, 0x41)
                    revert(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0x24)
                }
                mstore(64, newFreePtr)
            }
            function finalize_allocation(memPtr, size)
            {
                let newFreePtr := add(memPtr, and(add(size, 31), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0))
                if or(gt(newFreePtr, 0xffffffffffffffff), lt(newFreePtr, memPtr))
                {
                    mstore(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 35408467139433450592217433187231851964531694900788300625387963629091585785856)
                    mstore(4, 0x41)
                    revert(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0x24)
                }
                mstore(64, newFreePtr)
            }
            function array_allocation_size_string(length) -> size
            {
                if gt(length, 0xffffffffffffffff)
                {
                    mstore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856)
                    mstore(4, 0x41)
                    revert(0, 0x24)
                }
                size := add(and(add(length, 31), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0), 0x20)
            }
            function calldata_array_index_access_bytes32_dyn_calldata(base_ref, length, index) -> addr
            {
                if iszero(lt(index, length))
                {
                    mstore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856)
                    mstore(4, 0x32)
                    revert(0, 0x24)
                }
                addr := add(base_ref, shl(5, index))
            }
            function array_allocation_size_array_array_bytes32_dyn_dyn(length) -> size
            {
                if gt(length, 0xffffffffffffffff)
                {
                    mstore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856)
                    mstore(4, 0x41)
                    revert(0, 0x24)
                }
                size := add(shl(5, length), 0x20)
            }
            function allocate_and_zero_memory_array_array_array_bytes32_dyn_dyn(length) -> memPtr
            {
                let _1 := array_allocation_size_array_array_bytes32_dyn_dyn(length)
                let memPtr_1 := mload(64)
                finalize_allocation(memPtr_1, _1)
                mstore(memPtr_1, length)
                memPtr := memPtr_1
                let _2 := add(array_allocation_size_array_array_bytes32_dyn_dyn(length), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0)
                let i := /** @src -1:-1:-1 */ 0
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                for { } lt(i, _2) { i := add(i, 32) }
                {
                    mstore(add(add(memPtr_1, i), 32), 96)
                }
            }
            function calldata_array_index_access_struct_MultiAttestationRequest_calldata_dyn_calldata(base_ref, length, index) -> addr
            {
                if iszero(lt(index, length))
                {
                    mstore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856)
                    mstore(4, 0x32)
                    revert(0, 0x24)
                }
                let addr_1 := /** @src -1:-1:-1 */ 0
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                let rel_offset_of_tail := calldataload(add(base_ref, shl(5, index)))
                if iszero(slt(rel_offset_of_tail, add(sub(calldatasize(), base_ref), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc1)))
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                addr_1 := add(base_ref, rel_offset_of_tail)
                addr := addr_1
            }
            function access_calldata_tail_array_struct_AttestationRequestData_calldata_dyn_calldata(base_ref, ptr_to_tail) -> addr, length
            {
                let rel_offset_of_tail := calldataload(ptr_to_tail)
                if iszero(slt(rel_offset_of_tail, add(sub(calldatasize(), base_ref), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe1))) { revert(0, 0) }
                let addr_1 := add(base_ref, rel_offset_of_tail)
                length := calldataload(addr_1)
                if gt(length, 0xffffffffffffffff) { revert(0, 0) }
                addr := add(addr_1, 0x20)
                if sgt(addr, sub(calldatasize(), shl(5, length))) { revert(0, 0) }
            }
            function abi_decode_struct_AttestationRequestData(headStart, end) -> value
            {
                if slt(sub(end, headStart), 0xc0) { revert(0, 0) }
                let memPtr := mload(64)
                finalize_allocation_16860(memPtr)
                value := memPtr
                mstore(memPtr, abi_decode_address(headStart))
                let value_1 := calldataload(add(headStart, 32))
                if iszero(eq(value_1, and(value_1, 0xffffffffffffffff)))
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                mstore(add(memPtr, 32), value_1)
                let value_2 := calldataload(add(headStart, 64))
                if iszero(eq(value_2, iszero(iszero(value_2))))
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                mstore(add(memPtr, 64), value_2)
                mstore(add(memPtr, 96), calldataload(add(headStart, 96)))
                let offset := calldataload(add(headStart, 128))
                if gt(offset, 0xffffffffffffffff)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                let _1 := add(headStart, offset)
                if iszero(slt(add(_1, 0x1f), end))
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                let length := calldataload(_1)
                let _2 := array_allocation_size_string(length)
                let memPtr_1 := mload(64)
                finalize_allocation(memPtr_1, _2)
                mstore(memPtr_1, length)
                if gt(add(add(_1, length), 32), end)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                calldatacopy(add(memPtr_1, 32), add(_1, 32), length)
                mstore(add(add(memPtr_1, length), 32), /** @src -1:-1:-1 */ 0)
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                mstore(add(memPtr, 128), memPtr_1)
                mstore(add(memPtr, 160), calldataload(add(headStart, 160)))
            }
            function abi_decode_available_length_array_struct_AttestationRequestData_dyn(offset, length, end) -> array
            {
                let _1 := array_allocation_size_array_array_bytes32_dyn_dyn(length)
                let memPtr := mload(64)
                finalize_allocation(memPtr, _1)
                array := memPtr
                let dst := memPtr
                mstore(memPtr, length)
                dst := add(memPtr, 0x20)
                let srcEnd := add(offset, shl(5, length))
                if gt(srcEnd, end)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                let src := offset
                for { } lt(src, srcEnd) { src := add(src, 0x20) }
                {
                    let innerOffset := calldataload(src)
                    if gt(innerOffset, 0xffffffffffffffff)
                    {
                        revert(/** @src -1:-1:-1 */ 0, 0)
                    }
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    mstore(dst, abi_decode_struct_AttestationRequestData(add(offset, innerOffset), end))
                    dst := add(dst, 0x20)
                }
            }
            function checked_sub_uint256(x, y) -> diff
            {
                diff := sub(x, y)
                if gt(diff, x)
                {
                    mstore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856)
                    mstore(4, 0x11)
                    revert(0, 0x24)
                }
            }
            function memory_array_index_access_array_array_bytes32_dyn_dyn(baseRef) -> addr
            {
                if iszero(mload(baseRef))
                {
                    mstore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856)
                    mstore(4, 0x32)
                    revert(0, 0x24)
                }
                addr := add(baseRef, 32)
            }
            function memory_array_index_access_array_bytes32_dyn_dyn(baseRef, index) -> addr
            {
                if iszero(lt(index, mload(baseRef)))
                {
                    mstore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856)
                    mstore(4, 0x32)
                    revert(0, 0x24)
                }
                addr := add(add(baseRef, shl(5, index)), 32)
            }
            function allocate_and_zero_memory_array_array_struct_RevocationRequestData_dyn() -> memPtr
            {
                let size := /** @src -1:-1:-1 */ 0
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                if gt(/** @src 11:9338:9339  "1" */ 0x01, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffff)
                {
                    mstore(/** @src -1:-1:-1 */ size, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 35408467139433450592217433187231851964531694900788300625387963629091585785856)
                    mstore(4, 0x41)
                    revert(/** @src -1:-1:-1 */ size, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0x24)
                }
                size := add(shl(5, /** @src 11:9338:9339  "1" */ 0x01), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0x20)
                let memPtr_1 := mload(64)
                finalize_allocation(memPtr_1, size)
                mstore(memPtr_1, /** @src 11:9338:9339  "1" */ 0x01)
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                memPtr := memPtr_1
                let size_1 := /** @src -1:-1:-1 */ 0
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                if gt(/** @src 11:9338:9339  "1" */ 0x01, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffff)
                {
                    mstore(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 35408467139433450592217433187231851964531694900788300625387963629091585785856)
                    mstore(4, 0x41)
                    revert(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0x24)
                }
                size_1 := size
                let _1 := add(size, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0)
                let i := /** @src -1:-1:-1 */ 0
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                for { } lt(i, _1) { i := add(i, 32) }
                {
                    let memPtr_2 := mload(64)
                    finalize_allocation_16863(memPtr_2)
                    mstore(memPtr_2, /** @src -1:-1:-1 */ 0)
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    mstore(add(memPtr_2, 32), /** @src -1:-1:-1 */ 0)
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    mstore(add(add(memPtr_1, i), 32), memPtr_2)
                }
            }
            function abi_decode_struct_RevocationRequestData(end) -> value
            {
                if slt(add(end, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdc), 0x40) { revert(0, 0) }
                let memPtr := mload(0x40)
                finalize_allocation_16863(memPtr)
                value := memPtr
                mstore(memPtr, calldataload(/** @src 11:9364:9376  "request.data" */ 36))
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                mstore(add(memPtr, 32), calldataload(68))
            }
            function abi_decode_available_length_array_struct_RevocationRequestData_dyn(offset, length, end) -> array
            {
                let _1 := array_allocation_size_array_array_bytes32_dyn_dyn(length)
                let memPtr := mload(64)
                finalize_allocation(memPtr, _1)
                array := memPtr
                let dst := memPtr
                mstore(memPtr, length)
                dst := add(memPtr, 0x20)
                let srcEnd := add(offset, shl(6, length))
                if gt(srcEnd, end)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                let src := offset
                for { } lt(src, srcEnd) { src := add(src, 64) }
                {
                    let value := /** @src -1:-1:-1 */ 0
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    if slt(sub(end, src), 64)
                    {
                        revert(/** @src -1:-1:-1 */ value, value)
                    }
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    let memPtr_1 := mload(64)
                    finalize_allocation_16863(memPtr_1)
                    value := memPtr_1
                    mstore(memPtr_1, calldataload(src))
                    mstore(add(memPtr_1, 0x20), calldataload(add(src, 0x20)))
                    mstore(dst, memPtr_1)
                    dst := add(dst, 0x20)
                }
            }
            function calldata_array_index_access_struct_MultiDelegatedAttestationRequest_calldata_dyn_calldata(base_ref, length, index) -> addr
            {
                if iszero(lt(index, length))
                {
                    mstore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856)
                    mstore(4, 0x32)
                    revert(0, 0x24)
                }
                let addr_1 := /** @src -1:-1:-1 */ 0
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                let rel_offset_of_tail := calldataload(add(base_ref, shl(5, index)))
                if iszero(slt(rel_offset_of_tail, add(sub(calldatasize(), base_ref), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff81)))
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                addr_1 := add(base_ref, rel_offset_of_tail)
                addr := addr_1
            }
            function access_calldata_tail_array_struct_EIP712Signature_calldata_dyn_calldata(base_ref, ptr_to_tail) -> addr, length
            {
                let rel_offset_of_tail := calldataload(ptr_to_tail)
                if iszero(slt(rel_offset_of_tail, add(sub(calldatasize(), base_ref), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe1))) { revert(0, 0) }
                let addr_1 := add(base_ref, rel_offset_of_tail)
                length := calldataload(addr_1)
                if gt(length, 0xffffffffffffffff) { revert(0, 0) }
                addr := add(addr_1, 0x20)
                if sgt(addr, sub(calldatasize(), mul(length, 0x60))) { revert(0, 0) }
            }
            function access_calldata_tail_struct_AttestationRequestData_calldata(base_ref, ptr_to_tail) -> addr
            {
                let rel_offset_of_tail := calldataload(ptr_to_tail)
                if iszero(slt(rel_offset_of_tail, add(sub(calldatasize(), base_ref), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff41))) { revert(0, 0) }
                addr := add(base_ref, rel_offset_of_tail)
            }
            function read_from_calldatat_address(ptr) -> returnValue
            {
                let value := calldataload(ptr)
                if iszero(eq(value, and(value, 0xffffffffffffffffffffffffffffffffffffffff))) { revert(0, 0) }
                returnValue := value
            }
            function abi_decode_struct_EIP712Signature(headStart, end) -> value
            {
                if slt(sub(end, headStart), 0x60) { revert(0, 0) }
                let memPtr := mload(64)
                finalize_allocation_16869(memPtr)
                value := memPtr
                let value_1 := calldataload(headStart)
                if iszero(eq(value_1, and(value_1, 0xff)))
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                mstore(memPtr, value_1)
                mstore(add(memPtr, 32), calldataload(add(headStart, 32)))
                mstore(add(memPtr, 64), calldataload(add(headStart, 64)))
            }
            function allocate_and_zero_memory_struct_struct_Attestation() -> memPtr
            {
                let memPtr_1 := mload(64)
                finalize_allocation_16871(memPtr_1)
                memPtr := memPtr_1
                mstore(memPtr_1, /** @src -1:-1:-1 */ 0)
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                mstore(add(memPtr_1, 32), /** @src -1:-1:-1 */ 0)
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                mstore(add(memPtr_1, 64), /** @src -1:-1:-1 */ 0)
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                mstore(add(memPtr_1, 96), /** @src -1:-1:-1 */ 0)
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                mstore(add(memPtr_1, 128), /** @src -1:-1:-1 */ 0)
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                mstore(add(memPtr_1, 160), /** @src -1:-1:-1 */ 0)
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                mstore(add(memPtr_1, 192), /** @src -1:-1:-1 */ 0)
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                mstore(add(memPtr_1, 224), /** @src -1:-1:-1 */ 0)
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                mstore(add(memPtr_1, 256), /** @src -1:-1:-1 */ 0)
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                mstore(add(memPtr_1, 288), 96)
            }
            function extract_byte_array_length(data) -> length
            {
                length := shr(1, data)
                let outOfPlaceEncoding := and(data, 1)
                if iszero(outOfPlaceEncoding) { length := and(length, 0x7f) }
                if eq(outOfPlaceEncoding, lt(length, 32))
                {
                    mstore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856)
                    mstore(4, 0x22)
                    revert(0, 0x24)
                }
            }
            function read_from_storage_reference_type_struct_Attestation(slot) -> value
            {
                let memPtr := mload(64)
                finalize_allocation_16871(memPtr)
                value := memPtr
                mstore(memPtr, sload(slot))
                mstore(add(memPtr, 32), sload(add(slot, 1)))
                let _1 := sload(add(slot, 2))
                mstore(add(memPtr, 64), and(_1, 0xffffffffffffffff))
                mstore(add(memPtr, 96), and(shr(64, _1), 0xffffffffffffffff))
                mstore(add(memPtr, 128), and(shr(128, _1), 0xffffffffffffffff))
                mstore(add(memPtr, 160), sload(add(slot, 3)))
                mstore(add(memPtr, 192), and(sload(add(slot, 4)), 0xffffffffffffffffffffffffffffffffffffffff))
                let _2 := sload(add(slot, 5))
                mstore(add(memPtr, 224), and(_2, 0xffffffffffffffffffffffffffffffffffffffff))
                mstore(add(memPtr, 256), iszero(iszero(and(shr(160, _2), 0xff))))
                let _3 := add(slot, 6)
                let memPtr_1 := mload(64)
                let ret := /** @src -1:-1:-1 */ 0
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                let slotValue := sload(_3)
                let length := extract_byte_array_length(slotValue)
                mstore(memPtr_1, length)
                switch and(slotValue, 1)
                case 0 {
                    mstore(add(memPtr_1, 32), and(slotValue, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00))
                    ret := add(add(memPtr_1, shl(5, iszero(iszero(length)))), 32)
                }
                case 1 {
                    mstore(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _3)
                    let dataPos := keccak256(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 32)
                    let i := /** @src -1:-1:-1 */ 0
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    for { } lt(i, length) { i := add(i, 32) }
                    {
                        mstore(add(add(memPtr_1, i), 32), sload(dataPos))
                        dataPos := add(dataPos, 1)
                    }
                    ret := add(add(memPtr_1, i), 32)
                }
                finalize_allocation(memPtr_1, sub(ret, memPtr_1))
                mstore(add(memPtr, 288), memPtr_1)
            }
            function allocate_and_zero_memory_array_array_struct_AttestationRequestData_dyn() -> memPtr
            {
                let size := /** @src -1:-1:-1 */ 0
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                if gt(/** @src 11:3467:3468  "1" */ 0x01, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffff)
                {
                    mstore(/** @src -1:-1:-1 */ size, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 35408467139433450592217433187231851964531694900788300625387963629091585785856)
                    mstore(4, 0x41)
                    revert(/** @src -1:-1:-1 */ size, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0x24)
                }
                size := add(shl(5, /** @src 11:3467:3468  "1" */ 0x01), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0x20)
                let memPtr_1 := mload(64)
                finalize_allocation(memPtr_1, size)
                mstore(memPtr_1, /** @src 11:3467:3468  "1" */ 0x01)
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                memPtr := memPtr_1
                let size_1 := /** @src -1:-1:-1 */ 0
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                if gt(/** @src 11:3467:3468  "1" */ 0x01, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffff)
                {
                    mstore(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 35408467139433450592217433187231851964531694900788300625387963629091585785856)
                    mstore(4, 0x41)
                    revert(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0x24)
                }
                size_1 := size
                let _1 := add(size, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0)
                let i := /** @src -1:-1:-1 */ 0
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                for { } lt(i, _1) { i := add(i, 32) }
                {
                    let memPtr_2 := mload(64)
                    finalize_allocation_16860(memPtr_2)
                    mstore(memPtr_2, /** @src -1:-1:-1 */ 0)
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    mstore(add(memPtr_2, 32), /** @src -1:-1:-1 */ 0)
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    mstore(add(memPtr_2, 64), /** @src -1:-1:-1 */ 0)
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    mstore(add(memPtr_2, 96), /** @src -1:-1:-1 */ 0)
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    mstore(add(memPtr_2, 128), 96)
                    mstore(add(memPtr_2, 160), /** @src -1:-1:-1 */ 0)
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    mstore(add(add(memPtr_1, i), 32), memPtr_2)
                }
            }
            /// @ast-id 3827 @src 11:15170:15279  "function isAttestationValid(bytes32 uid) public view returns (bool) {..."
            function fun_isAttestationValid(var_uid) -> var_
            {
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                mstore(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ var_uid)
                mstore(0x20, /** @src 11:15255:15258  "_db" */ 0x01)
                /// @src 11:15248:15272  "return _db[uid].uid != 0"
                var_ := /** @src 11:15255:15272  "_db[uid].uid != 0" */ iszero(iszero(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ sload(keccak256(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0x40))))
            }
            /// @ast-id 4775 @src 11:29280:29649  "function _revokeOffchain(address revoker, bytes32 data, uint64 time) private {..."
            function fun_revokeOffchain(var_revoker, var_data, var_time)
            {
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                let _1 := and(var_revoker, 0xffffffffffffffffffffffffffffffffffffffff)
                mstore(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _1)
                mstore(0x20, /** @src 11:29431:29451  "_revocationsOffchain" */ 0x03)
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                let dataSlot := keccak256(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0x40)
                mstore(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ var_data)
                mstore(0x20, dataSlot)
                /// @src 11:29472:29556  "if (revocations[data] != 0) {..."
                if /** @src 11:29476:29498  "revocations[data] != 0" */ iszero(iszero(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(sload(keccak256(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0x40)), 0xffffffffffffffff)))
                /// @src 11:29472:29556  "if (revocations[data] != 0) {..."
                {
                    /// @src 11:29521:29545  "AlreadyRevokedOffchain()"
                    mstore(/** @src -1:-1:-1 */ 0, /** @src 11:29521:29545  "AlreadyRevokedOffchain()" */ 0xec9d6eeb00000000000000000000000000000000000000000000000000000000)
                    revert(/** @src -1:-1:-1 */ 0, /** @src 11:29521:29545  "AlreadyRevokedOffchain()" */ 4)
                }
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                mstore(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ var_data)
                mstore(0x20, dataSlot)
                let dataSlot_1 := keccak256(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0x40)
                sstore(/** @src 11:29566:29583  "revocations[data]" */ dataSlot_1, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ or(and(sload(/** @src 11:29566:29583  "revocations[data]" */ dataSlot_1), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000), and(/** @src 11:29566:29590  "revocations[data] = time" */ var_time, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffff)))
                /// @src 11:29606:29642  "RevokedOffchain(revoker, data, time)"
                log4(/** @src -1:-1:-1 */ 0, 0, /** @src 11:29606:29642  "RevokedOffchain(revoker, data, time)" */ 0x92a1f7a41a7c585a8b09e25b195e225b1d43248daca46b0faf9e0792777a2229, _1, var_data, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(/** @src 11:29606:29642  "RevokedOffchain(revoker, data, time)" */ var_time, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffff))
            }
            function allocate_and_zero_memory_struct_struct_AttestationsResult() -> memPtr
            {
                let memPtr_1 := mload(64)
                finalize_allocation_16863(memPtr_1)
                memPtr := memPtr_1
                mstore(memPtr_1, /** @src -1:-1:-1 */ 0)
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                mstore(add(memPtr_1, 32), 96)
            }
            function allocate_and_zero_memory_array_array_bytes32_dyn(length) -> memPtr
            {
                let _1 := array_allocation_size_array_array_bytes32_dyn_dyn(length)
                let memPtr_1 := mload(64)
                finalize_allocation(memPtr_1, _1)
                mstore(memPtr_1, length)
                memPtr := memPtr_1
                calldatacopy(add(memPtr_1, 32), calldatasize(), add(array_allocation_size_array_array_bytes32_dyn_dyn(length), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0))
            }
            function abi_decode_bool_fromMemory(offset) -> value
            {
                value := mload(offset)
                if iszero(eq(value, iszero(iszero(value)))) { revert(0, 0) }
            }
            function abi_decode_struct_SchemaRecord_fromMemory(headStart, dataEnd) -> value0
            {
                if slt(sub(dataEnd, headStart), 32) { revert(0, 0) }
                let offset := mload(headStart)
                if gt(offset, 0xffffffffffffffff) { revert(0, 0) }
                let _1 := add(headStart, offset)
                if slt(sub(dataEnd, _1), 0x80)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                let memPtr := mload(64)
                finalize_allocation_16801(memPtr)
                mstore(memPtr, mload(_1))
                let value := mload(add(_1, 32))
                if iszero(eq(value, and(value, 0xffffffffffffffffffffffffffffffffffffffff)))
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                mstore(add(memPtr, 32), value)
                mstore(add(memPtr, 64), abi_decode_bool_fromMemory(add(_1, 64)))
                let offset_1 := mload(add(_1, 96))
                if gt(offset_1, 0xffffffffffffffff)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                let _2 := add(_1, offset_1)
                if iszero(slt(add(_2, 0x1f), dataEnd))
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                let length := mload(_2)
                let _3 := array_allocation_size_string(length)
                let memPtr_1 := mload(64)
                finalize_allocation(memPtr_1, _3)
                mstore(memPtr_1, length)
                if gt(add(add(_2, length), 32), dataEnd)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                copy_memory_to_memory_with_cleanup(add(_2, 32), add(memPtr_1, 32), length)
                mstore(add(memPtr, 96), memPtr_1)
                value0 := memPtr
            }
            /// @src 16:138:139  "0"
            function allocate_and_zero_memory_array_array_struct_Attestation_dyn(length) -> memPtr
            {
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                let _1 := array_allocation_size_array_array_bytes32_dyn_dyn(length)
                let memPtr_1 := mload(64)
                finalize_allocation(memPtr_1, _1)
                mstore(memPtr_1, length)
                /// @src 16:138:139  "0"
                memPtr := memPtr_1
                let _2 := add(array_allocation_size_array_array_bytes32_dyn_dyn(length), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0)
                let i := /** @src -1:-1:-1 */ 0
                /// @src 16:138:139  "0"
                for { } lt(i, _2) { i := add(i, 32) }
                {
                    mstore(add(add(memPtr_1, i), 32), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ allocate_and_zero_memory_struct_struct_Attestation())
                }
            }
            /// @src 11:1790:1791  "0"
            function update_storage_value_offset_uint64_to_uint64(slot, value)
            {
                let _1 := sload(slot)
                sstore(slot, or(and(_1, 0xffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffff), and(shl(128, value), 0xffffffffffffffff00000000000000000000000000000000)))
            }
            /// @ast-id 4106 @src 11:16135:19054  "function _attest(..."
            function fun__attest(var_schema, var_data_mpos, var_attester, var_availableValue) -> var__mpos
            {
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                pop(allocate_and_zero_memory_struct_struct_AttestationsResult())
                /// @src 11:16376:16387  "data.length"
                let expr := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 11:16376:16387  "data.length" */ var_data_mpos)
                /// @src 11:16398:16427  "AttestationsResult memory res"
                let zero_struct_AttestationsResult_mpos := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ allocate_and_zero_memory_struct_struct_AttestationsResult()
                /// @src 11:16448:16469  "new bytes32[](length)"
                let expr_mpos := allocate_and_zero_memory_array_array_bytes32_dyn(expr)
                /// @src 11:16437:16469  "res.uids = new bytes32[](length)"
                mstore(/** @src 11:16437:16445  "res.uids" */ add(zero_struct_AttestationsResult_mpos, 32), /** @src 11:16437:16469  "res.uids = new bytes32[](length)" */ expr_mpos)
                /// @src 11:16595:16628  "_schemaRegistry.getSchema(schema)"
                let _1 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(64)
                /// @src 11:16595:16628  "_schemaRegistry.getSchema(schema)"
                mstore(_1, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xa2ea7c6e00000000000000000000000000000000000000000000000000000000)
                mstore(/** @src 11:16595:16628  "_schemaRegistry.getSchema(schema)" */ add(_1, 4), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ var_schema)
                /// @src 11:16595:16628  "_schemaRegistry.getSchema(schema)"
                let _2 := staticcall(gas(), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(/** @src 11:16595:16610  "_schemaRegistry" */ loadimmutable("3001"), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffff), /** @src 11:16595:16628  "_schemaRegistry.getSchema(schema)" */ _1, 36, _1, /** @src -1:-1:-1 */ 0)
                /// @src 11:16595:16628  "_schemaRegistry.getSchema(schema)"
                if iszero(_2)
                {
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    let pos := mload(64)
                    returndatacopy(pos, /** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ returndatasize())
                    revert(pos, returndatasize())
                }
                /// @src 11:16595:16628  "_schemaRegistry.getSchema(schema)"
                let expr_mpos_1 := /** @src -1:-1:-1 */ 0
                /// @src 11:16595:16628  "_schemaRegistry.getSchema(schema)"
                if _2
                {
                    let _3 := returndatasize()
                    returndatacopy(_1, /** @src -1:-1:-1 */ 0, /** @src 11:16595:16628  "_schemaRegistry.getSchema(schema)" */ _3)
                    finalize_allocation(_1, _3)
                    expr_mpos_1 := abi_decode_struct_SchemaRecord_fromMemory(_1, add(_1, _3))
                }
                /// @src 11:16638:16720  "if (schemaRecord.uid == EMPTY_UID) {..."
                if /** @src 11:16642:16671  "schemaRecord.uid == EMPTY_UID" */ iszero(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 11:16642:16658  "schemaRecord.uid" */ expr_mpos_1))
                /// @src 11:16638:16720  "if (schemaRecord.uid == EMPTY_UID) {..."
                {
                    /// @src 11:16694:16709  "InvalidSchema()"
                    mstore(/** @src -1:-1:-1 */ 0, /** @src 11:16694:16709  "InvalidSchema()" */ 0xbf37b20e00000000000000000000000000000000000000000000000000000000)
                    revert(/** @src -1:-1:-1 */ 0, /** @src 11:16595:16628  "_schemaRegistry.getSchema(schema)" */ 4)
                }
                /// @src 11:16766:16791  "new Attestation[](length)"
                let expr_mpos_2 := allocate_and_zero_memory_array_array_struct_Attestation_dyn(expr)
                /// @src 11:16827:16848  "new uint256[](length)"
                let expr_mpos_3 := allocate_and_zero_memory_array_array_bytes32_dyn(expr)
                /// @src 11:16864:16877  "uint256 i = 0"
                let var_i := /** @src -1:-1:-1 */ 0
                /// @src 11:16859:18915  "for (uint256 i = 0; i < length; ) {..."
                for { }
                /** @src 11:16879:16889  "i < length" */ lt(var_i, expr)
                /// @src 11:16864:16877  "uint256 i = 0"
                { }
                {
                    /// @src 11:16947:16954  "data[i]"
                    let _mpos := mload(memory_array_index_access_array_bytes32_dyn_dyn(var_data_mpos, var_i))
                    /// @src 11:17068:17090  "request.expirationTime"
                    let _4 := add(_mpos, /** @src 11:16437:16445  "res.uids" */ 32)
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    let cleaned := and(/** @src 16:138:139  "0" */ mload(/** @src 11:17068:17090  "request.expirationTime" */ _4), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffff)
                    /// @src 11:17068:17149  "request.expirationTime != NO_EXPIRATION_TIME && request.expirationTime <= _time()"
                    let expr_1 := /** @src 11:17068:17112  "request.expirationTime != NO_EXPIRATION_TIME" */ iszero(iszero(cleaned))
                    /// @src 11:17068:17149  "request.expirationTime != NO_EXPIRATION_TIME && request.expirationTime <= _time()"
                    if expr_1
                    {
                        expr_1 := /** @src 11:17116:17149  "request.expirationTime <= _time()" */ iszero(gt(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ cleaned, and(/** @src 11:29893:29908  "block.timestamp" */ timestamp(), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffff)))
                    }
                    /// @src 11:17064:17214  "if (request.expirationTime != NO_EXPIRATION_TIME && request.expirationTime <= _time()) {..."
                    if expr_1
                    {
                        /// @src 11:17176:17199  "InvalidExpirationTime()"
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 11:17176:17199  "InvalidExpirationTime()" */ 0x08e8b93700000000000000000000000000000000000000000000000000000000)
                        revert(/** @src -1:-1:-1 */ 0, /** @src 11:16595:16628  "_schemaRegistry.getSchema(schema)" */ 4)
                    }
                    /// @src 11:17336:17380  "!schemaRecord.revocable && request.revocable"
                    let expr_2 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ iszero(/** @src 11:1790:1791  "0" */ mload(/** @src 11:17337:17359  "schemaRecord.revocable" */ add(expr_mpos_1, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 64)))
                    /// @src 11:17336:17380  "!schemaRecord.revocable && request.revocable"
                    if expr_2
                    {
                        expr_2 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ iszero(iszero(/** @src 11:1790:1791  "0" */ mload(/** @src 11:17363:17380  "request.revocable" */ add(_mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 64))))
                    }
                    /// @src 11:17332:17435  "if (!schemaRecord.revocable && request.revocable) {..."
                    if expr_2
                    {
                        /// @src 11:17407:17420  "Irrevocable()"
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 11:17407:17420  "Irrevocable()" */ 0x157bd4c300000000000000000000000000000000000000000000000000000000)
                        revert(/** @src -1:-1:-1 */ 0, /** @src 11:16595:16628  "_schemaRegistry.getSchema(schema)" */ 4)
                    }
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    let _5 := mload(/** @src 11:17584:17598  "request.refUID" */ add(_mpos, 96))
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    let cleaned_1 := and(/** @src 16:138:139  "0" */ mload(/** @src 11:17663:17685  "request.expirationTime" */ _4), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffff)
                    let cleaned_2 := and(mload(/** @src 11:17749:17766  "request.recipient" */ _mpos), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffff)
                    let cleaned_3 := iszero(iszero(/** @src 11:1790:1791  "0" */ mload(/** @src 11:17831:17848  "request.revocable" */ add(_mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 64))))
                    /// @src 11:17872:17884  "request.data"
                    let _mpos_1 := mload(add(_mpos, 128))
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    let memPtr := mload(64)
                    finalize_allocation_16871(memPtr)
                    mstore(memPtr, /** @src -1:-1:-1 */ 0)
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    mstore(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, /** @src 11:16437:16445  "res.uids" */ 32), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ var_schema)
                    mstore(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 64), and(/** @src 11:29893:29908  "block.timestamp" */ timestamp(), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffff))
                    mstore(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, /** @src 11:17584:17598  "request.refUID" */ 96), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ cleaned_1)
                    mstore(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, /** @src 11:17872:17884  "request.data" */ 128), /** @src -1:-1:-1 */ 0)
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    mstore(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, 160), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _5)
                    mstore(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, 192), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ cleaned_2)
                    mstore(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 224), and(var_attester, 0xffffffffffffffffffffffffffffffffffffffff))
                    mstore(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, 256), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ cleaned_3)
                    mstore(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, 288), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _mpos_1)
                    /// @src 11:18025:18036  "bytes32 uid"
                    let var_uid := /** @src -1:-1:-1 */ 0
                    /// @src 11:18025:18036  "bytes32 uid"
                    var_uid := /** @src -1:-1:-1 */ var_uid
                    /// @src 11:18050:18065  "uint32 bump = 0"
                    let var_bump := /** @src -1:-1:-1 */ 0
                    /// @src 11:18079:18326  "while (true) {..."
                    for { }
                    /** @src 11:3467:3468  "1" */ 0x01
                    /// @src 11:18079:18326  "while (true) {..."
                    { }
                    {
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        let _6 := mload(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, /** @src 11:16437:16445  "res.uids" */ 32))
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        let _7 := mload(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, 192))
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        let _8 := mload(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 224))
                        /// @src 16:138:139  "0"
                        let _9 := mload(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 64))
                        /// @src 16:138:139  "0"
                        let _10 := mload(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, /** @src 11:17584:17598  "request.refUID" */ 96))
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        let cleaned_4 := iszero(iszero(/** @src 11:1790:1791  "0" */ mload(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, 256))))
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        let _11 := mload(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, 160))
                        /// @src 11:27187:27203  "attestation.data"
                        let _mpos_2 := mload(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, 288))
                        /// @src 11:26855:27247  "abi.encodePacked(..."
                        let expr_mpos_4 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(64)
                        /// @src 11:26855:27247  "abi.encodePacked(..."
                        let _12 := add(expr_mpos_4, /** @src 11:16437:16445  "res.uids" */ 32)
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        mstore(_12, _6)
                        mstore(add(/** @src 11:26855:27247  "abi.encodePacked(..." */ expr_mpos_4, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 64), and(shl(/** @src 11:17584:17598  "request.refUID" */ 96, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _7), 0xffffffffffffffffffffffffffffffffffffffff000000000000000000000000))
                        mstore(add(/** @src 11:26855:27247  "abi.encodePacked(..." */ expr_mpos_4, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 84), and(shl(/** @src 11:17584:17598  "request.refUID" */ 96, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _8), 0xffffffffffffffffffffffffffffffffffffffff000000000000000000000000))
                        mstore(add(/** @src 11:26855:27247  "abi.encodePacked(..." */ expr_mpos_4, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 104), and(shl(/** @src 11:17482:17899  "Attestation({..." */ 192, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _9), 0xffffffffffffffff000000000000000000000000000000000000000000000000))
                        mstore(add(/** @src 11:26855:27247  "abi.encodePacked(..." */ expr_mpos_4, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 112), and(shl(/** @src 11:17482:17899  "Attestation({..." */ 192, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _10), 0xffffffffffffffff000000000000000000000000000000000000000000000000))
                        mstore(add(/** @src 11:26855:27247  "abi.encodePacked(..." */ expr_mpos_4, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 120), shl(248, cleaned_4))
                        mstore(add(/** @src 11:26855:27247  "abi.encodePacked(..." */ expr_mpos_4, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 121), _11)
                        let length := mload(_mpos_2)
                        copy_memory_to_memory_with_cleanup(add(_mpos_2, /** @src 11:16437:16445  "res.uids" */ 32), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ add(/** @src 11:26855:27247  "abi.encodePacked(..." */ expr_mpos_4, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 153), length)
                        let _13 := add(/** @src 11:26855:27247  "abi.encodePacked(..." */ expr_mpos_4, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ length)
                        mstore(add(_13, 153), and(shl(224, var_bump), 0xffffffff00000000000000000000000000000000000000000000000000000000))
                        /// @src 11:26855:27247  "abi.encodePacked(..."
                        let _14 := add(sub(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _13, /** @src 11:26855:27247  "abi.encodePacked(..." */ expr_mpos_4), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 153)
                        /// @src 11:26855:27247  "abi.encodePacked(..."
                        mstore(expr_mpos_4, add(_14, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe4))
                        finalize_allocation(expr_mpos_4, add(_14, /** @src 11:16595:16628  "_schemaRegistry.getSchema(schema)" */ 4))
                        /// @src 11:18110:18142  "uid = _getUID(attestation, bump)"
                        var_uid := /** @src 11:26828:27261  "keccak256(..." */ keccak256(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _12, mload(/** @src 11:26828:27261  "keccak256(..." */ expr_mpos_4))
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ var_uid)
                        mstore(/** @src 11:16437:16445  "res.uids" */ 32, /** @src 11:3467:3468  "1" */ 0x01)
                        /// @src 11:18160:18237  "if (_db[uid].uid == EMPTY_UID) {..."
                        if /** @src 11:18164:18189  "_db[uid].uid == EMPTY_UID" */ iszero(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ sload(keccak256(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 64)))
                        /// @src 11:18160:18237  "if (_db[uid].uid == EMPTY_UID) {..."
                        {
                            /// @src 11:18213:18218  "break"
                            break
                        }
                        /// @src 11:18287:18293  "++bump"
                        var_bump := /** @src 11:1790:1791  "0" */ and(add(/** @src 11:18287:18293  "++bump" */ var_bump, /** @src 11:3467:3468  "1" */ 0x01), /** @src 11:1790:1791  "0" */ 0xffffffff)
                    }
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    mstore(memPtr, var_uid)
                    mstore(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ var_uid)
                    mstore(/** @src 11:16437:16445  "res.uids" */ 32, /** @src 11:3467:3468  "1" */ 0x01)
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    let dataSlot := keccak256(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 64)
                    /// @src 11:1790:1791  "0"
                    sstore(dataSlot, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 11:1790:1791  "0" */ memPtr))
                    sstore(add(dataSlot, /** @src 11:3467:3468  "1" */ 0x01), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, /** @src 11:16437:16445  "res.uids" */ 32)))
                    /// @src 11:1790:1791  "0"
                    let memberSlot := add(dataSlot, 2)
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    sstore(memberSlot, or(and(sload(memberSlot), 0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000), and(and(/** @src 16:138:139  "0" */ mload(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 64)), 0xffffffffffffffff), 0xffffffffffffffff)))
                    /// @src 16:138:139  "0"
                    let _15 := mload(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, /** @src 11:17584:17598  "request.refUID" */ 96))
                    /// @src 11:1790:1791  "0"
                    let _16 := sload(memberSlot)
                    sstore(memberSlot, or(and(_16, 0xffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff), and(shl(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 64, _15), /** @src 11:1790:1791  "0" */ 0xffffffffffffffff0000000000000000)))
                    update_storage_value_offset_uint64_to_uint64(memberSlot, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(/** @src 16:138:139  "0" */ mload(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, /** @src 11:17872:17884  "request.data" */ 128)), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffff))
                    /// @src 11:1790:1791  "0"
                    sstore(add(dataSlot, 3), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, 160)))
                    /// @src 11:1790:1791  "0"
                    let value := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(mload(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, 192)), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffff)
                    /// @src 11:1790:1791  "0"
                    let slot := add(dataSlot, /** @src 11:16595:16628  "_schemaRegistry.getSchema(schema)" */ 4)
                    /// @src 11:1790:1791  "0"
                    sstore(slot, or(and(sload(slot), 0xffffffffffffffffffffffff0000000000000000000000000000000000000000), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(/** @src 11:1790:1791  "0" */ value, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffff)))
                    /// @src 11:1790:1791  "0"
                    let memberSlot_1 := add(dataSlot, 5)
                    sstore(memberSlot_1, or(and(sload(memberSlot_1), 0xffffffffffffffffffffffff0000000000000000000000000000000000000000), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(and(mload(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 224)), 0xffffffffffffffffffffffffffffffffffffffff), 0xffffffffffffffffffffffffffffffffffffffff)))
                    let cleaned_5 := iszero(iszero(/** @src 11:1790:1791  "0" */ mload(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, 256))))
                    /// @src 11:1790:1791  "0"
                    let _17 := sload(memberSlot_1)
                    sstore(memberSlot_1, or(and(_17, 0xffffffffffffffffffffff00ffffffffffffffffffffffffffffffffffffffff), and(shl(/** @src 11:17482:17899  "Attestation({..." */ 160, /** @src 11:1790:1791  "0" */ cleaned_5), 0xff0000000000000000000000000000000000000000)))
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    let _18 := mload(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, 288))
                    /// @src 11:1790:1791  "0"
                    let newLen := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 11:1790:1791  "0" */ _18)
                    if gt(newLen, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffff)
                    /// @src 11:1790:1791  "0"
                    {
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 35408467139433450592217433187231851964531694900788300625387963629091585785856)
                        mstore(/** @src 11:16595:16628  "_schemaRegistry.getSchema(schema)" */ 4, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0x41)
                        revert(/** @src -1:-1:-1 */ 0, /** @src 11:16595:16628  "_schemaRegistry.getSchema(schema)" */ 36)
                    }
                    /// @src 11:1790:1791  "0"
                    let _19 := extract_byte_array_length(sload(add(dataSlot, 6)))
                    if gt(_19, 31)
                    {
                        if gt(_19, newLen)
                        {
                            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                            mstore(/** @src -1:-1:-1 */ 0, /** @src 11:1790:1791  "0" */ add(dataSlot, 6))
                            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                            let data := keccak256(/** @src -1:-1:-1 */ 0, /** @src 11:16437:16445  "res.uids" */ 32)
                            /// @src 11:1790:1791  "0"
                            let newSlotCount := shr(5, add(newLen, 31))
                            if lt(newLen, /** @src 11:16437:16445  "res.uids" */ 32)
                            /// @src 11:1790:1791  "0"
                            {
                                newSlotCount := /** @src -1:-1:-1 */ 0
                            }
                            /// @src 11:1790:1791  "0"
                            let i := /** @src -1:-1:-1 */ 0
                            /// @src 11:1790:1791  "0"
                            for { }
                            lt(i, sub(shr(5, add(_19, 31)), newSlotCount))
                            {
                                i := add(i, /** @src 11:3467:3468  "1" */ 0x01)
                            }
                            /// @src 11:1790:1791  "0"
                            {
                                sstore(add(add(data, newSlotCount), i), /** @src -1:-1:-1 */ 0)
                            }
                        }
                    }
                    /// @src 11:1790:1791  "0"
                    let srcOffset := /** @src -1:-1:-1 */ 0
                    /// @src 11:1790:1791  "0"
                    srcOffset := /** @src 11:16437:16445  "res.uids" */ 32
                    /// @src 11:1790:1791  "0"
                    switch gt(newLen, 31)
                    case 1 {
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 11:1790:1791  "0" */ add(dataSlot, 6))
                        let dstPtr := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ keccak256(/** @src -1:-1:-1 */ 0, /** @src 11:16437:16445  "res.uids" */ srcOffset)
                        /// @src 11:1790:1791  "0"
                        let i_1 := /** @src -1:-1:-1 */ 0
                        /// @src 11:1790:1791  "0"
                        for { }
                        lt(i_1, and(newLen, /** @src 11:26855:27247  "abi.encodePacked(..." */ 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0))
                        /// @src 11:1790:1791  "0"
                        {
                            i_1 := add(i_1, /** @src 11:16437:16445  "res.uids" */ 32)
                        }
                        /// @src 11:1790:1791  "0"
                        {
                            sstore(dstPtr, mload(add(_18, srcOffset)))
                            dstPtr := add(dstPtr, /** @src 11:3467:3468  "1" */ 0x01)
                            /// @src 11:1790:1791  "0"
                            srcOffset := add(srcOffset, /** @src 11:16437:16445  "res.uids" */ 32)
                        }
                        /// @src 11:1790:1791  "0"
                        if lt(and(newLen, /** @src 11:26855:27247  "abi.encodePacked(..." */ 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0), /** @src 11:1790:1791  "0" */ newLen)
                        {
                            let lastValue := mload(add(_18, srcOffset))
                            sstore(dstPtr, and(lastValue, not(shr(and(shl(3, newLen), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 248), /** @src 11:1790:1791  "0" */ 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff))))
                        }
                        sstore(add(dataSlot, 6), add(shl(/** @src 11:3467:3468  "1" */ 0x01, /** @src 11:1790:1791  "0" */ newLen), /** @src 11:3467:3468  "1" */ 0x01))
                    }
                    default /// @src 11:1790:1791  "0"
                    {
                        let value_1 := /** @src -1:-1:-1 */ 0
                        /// @src 11:1790:1791  "0"
                        if newLen
                        {
                            value_1 := mload(add(_18, srcOffset))
                        }
                        sstore(add(dataSlot, 6), or(and(value_1, not(shr(shl(3, newLen), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff))), shl(/** @src 11:3467:3468  "1" */ 0x01, /** @src 11:1790:1791  "0" */ newLen)))
                    }
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    let _20 := mload(/** @src 11:17584:17598  "request.refUID" */ add(_mpos, 96))
                    /// @src 11:18412:18660  "if (request.refUID != 0) {..."
                    if /** @src 11:18416:18435  "request.refUID != 0" */ iszero(iszero(_20))
                    /// @src 11:18412:18660  "if (request.refUID != 0) {..."
                    {
                        /// @src 11:18547:18646  "if (!isAttestationValid(request.refUID)) {..."
                        if /** @src 11:18551:18586  "!isAttestationValid(request.refUID)" */ iszero(/** @src 11:18552:18586  "isAttestationValid(request.refUID)" */ fun_isAttestationValid(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _20))
                        /// @src 11:18547:18646  "if (!isAttestationValid(request.refUID)) {..."
                        {
                            /// @src 11:18617:18627  "NotFound()"
                            mstore(/** @src -1:-1:-1 */ 0, /** @src 11:18617:18627  "NotFound()" */ 0xc5723b5100000000000000000000000000000000000000000000000000000000)
                            revert(/** @src -1:-1:-1 */ 0, /** @src 11:16595:16628  "_schemaRegistry.getSchema(schema)" */ 4)
                        }
                    }
                    /// @src 11:18674:18703  "attestations[i] = attestation"
                    mstore(memory_array_index_access_array_bytes32_dyn_dyn(expr_mpos_2, var_i), memPtr)
                    pop(memory_array_index_access_array_bytes32_dyn_dyn(expr_mpos_2, var_i))
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    mstore(/** @src 11:18717:18742  "values[i] = request.value" */ memory_array_index_access_array_bytes32_dyn_dyn(expr_mpos_3, var_i), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 11:18729:18742  "request.value" */ add(_mpos, /** @src 11:17482:17899  "Attestation({..." */ 160)))
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    mstore(/** @src 11:18757:18774  "res.uids[i] = uid" */ memory_array_index_access_array_bytes32_dyn_dyn(/** @src 11:18757:18765  "res.uids" */ mload(/** @src 11:16437:16445  "res.uids" */ add(zero_struct_AttestationsResult_mpos, 32)), /** @src 11:18757:18774  "res.uids[i] = uid" */ var_i), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ var_uid)
                    let cleaned_6 := and(mload(/** @src 11:18803:18820  "request.recipient" */ _mpos), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffff)
                    /// @src 11:18794:18844  "Attested(request.recipient, attester, uid, schema)"
                    let _21 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(64)
                    mstore(_21, var_uid)
                    /// @src 11:18794:18844  "Attested(request.recipient, attester, uid, schema)"
                    log4(_21, /** @src 11:16437:16445  "res.uids" */ 32, /** @src 11:18794:18844  "Attested(request.recipient, attester, uid, schema)" */ 0x8bf46bf4cfd674fa735a3d63ec1c9ad4153f033c290341f3a588b75685141b35, cleaned_6, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(var_attester, 0xffffffffffffffffffffffffffffffffffffffff), /** @src 11:18794:18844  "Attested(request.recipient, attester, uid, schema)" */ var_schema)
                    /// @src 11:18887:18890  "++i"
                    var_i := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ add(/** @src 11:18887:18890  "++i" */ var_i, /** @src 11:3467:3468  "1" */ 0x01)
                }
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                mstore(zero_struct_AttestationsResult_mpos, /** @src 11:18941:19026  "_resolveAttestations(schemaRecord, attestations, values, false, availableValue, last)" */ fun__resolveAttestations(expr_mpos_1, expr_mpos_2, expr_mpos_3, var_availableValue, /** @src 11:3467:3468  "1" */ 0x01))
                /// @src 11:19037:19047  "return res"
                var__mpos := zero_struct_AttestationsResult_mpos
            }
            /// @ast-id 4106 @src 11:16135:19054  "function _attest(..."
            function fun_attest(var_schema, var_data_3864_mpos, var_attester, var_availableValue, var_last) -> var_mpos
            {
                mstore(0xc0, var_data_3864_mpos)
                mstore(0xa0, var_attester)
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                pop(allocate_and_zero_memory_struct_struct_AttestationsResult())
                /// @src 11:16376:16387  "data.length"
                let expr := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 11:16376:16387  "data.length" */ mload(0xc0))
                /// @src 11:16398:16427  "AttestationsResult memory res"
                mstore(0x80, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ allocate_and_zero_memory_struct_struct_AttestationsResult())
                /// @src 11:16448:16469  "new bytes32[](length)"
                let expr_3892_mpos := allocate_and_zero_memory_array_array_bytes32_dyn(expr)
                /// @src 11:16437:16469  "res.uids = new bytes32[](length)"
                mstore(/** @src 11:16437:16445  "res.uids" */ add(mload(0x80), 32), /** @src 11:16437:16469  "res.uids = new bytes32[](length)" */ expr_3892_mpos)
                /// @src 11:16595:16628  "_schemaRegistry.getSchema(schema)"
                let _1 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(64)
                /// @src 11:16595:16628  "_schemaRegistry.getSchema(schema)"
                mstore(_1, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xa2ea7c6e00000000000000000000000000000000000000000000000000000000)
                mstore(/** @src 11:16595:16628  "_schemaRegistry.getSchema(schema)" */ add(_1, 4), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ var_schema)
                /// @src 11:16595:16628  "_schemaRegistry.getSchema(schema)"
                let _2 := staticcall(gas(), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(/** @src 11:16595:16610  "_schemaRegistry" */ loadimmutable("3001"), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffff), /** @src 11:16595:16628  "_schemaRegistry.getSchema(schema)" */ _1, 36, _1, /** @src -1:-1:-1 */ 0)
                /// @src 11:16595:16628  "_schemaRegistry.getSchema(schema)"
                if iszero(_2)
                {
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    let pos := mload(64)
                    returndatacopy(pos, /** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ returndatasize())
                    revert(pos, returndatasize())
                }
                /// @src 11:16595:16628  "_schemaRegistry.getSchema(schema)"
                let expr_3901_mpos := /** @src -1:-1:-1 */ 0
                /// @src 11:16595:16628  "_schemaRegistry.getSchema(schema)"
                if _2
                {
                    let _3 := returndatasize()
                    returndatacopy(_1, /** @src -1:-1:-1 */ 0, /** @src 11:16595:16628  "_schemaRegistry.getSchema(schema)" */ _3)
                    finalize_allocation(_1, _3)
                    expr_3901_mpos := abi_decode_struct_SchemaRecord_fromMemory(_1, add(_1, _3))
                }
                /// @src 11:16638:16720  "if (schemaRecord.uid == EMPTY_UID) {..."
                if /** @src 11:16642:16671  "schemaRecord.uid == EMPTY_UID" */ iszero(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 11:16642:16658  "schemaRecord.uid" */ expr_3901_mpos))
                /// @src 11:16638:16720  "if (schemaRecord.uid == EMPTY_UID) {..."
                {
                    /// @src 11:16694:16709  "InvalidSchema()"
                    mstore(/** @src -1:-1:-1 */ 0, /** @src 11:16694:16709  "InvalidSchema()" */ 0xbf37b20e00000000000000000000000000000000000000000000000000000000)
                    revert(/** @src -1:-1:-1 */ 0, /** @src 11:16595:16628  "_schemaRegistry.getSchema(schema)" */ 4)
                }
                /// @src 11:16766:16791  "new Attestation[](length)"
                let expr_3922_mpos := allocate_and_zero_memory_array_array_struct_Attestation_dyn(expr)
                /// @src 11:16827:16848  "new uint256[](length)"
                let expr_3933_mpos := allocate_and_zero_memory_array_array_bytes32_dyn(expr)
                /// @src 11:16864:16877  "uint256 i = 0"
                let var_i := /** @src -1:-1:-1 */ 0
                /// @src 11:16859:18915  "for (uint256 i = 0; i < length; ) {..."
                for { }
                /** @src 11:16879:16889  "i < length" */ lt(var_i, expr)
                /// @src 11:16864:16877  "uint256 i = 0"
                { }
                {
                    /// @src 11:16947:16954  "data[i]"
                    let _320_mpos := mload(memory_array_index_access_array_bytes32_dyn_dyn(mload(0xc0), var_i))
                    /// @src 11:17068:17090  "request.expirationTime"
                    let _4 := add(_320_mpos, /** @src 11:16437:16445  "res.uids" */ 32)
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    let cleaned := and(/** @src 16:138:139  "0" */ mload(/** @src 11:17068:17090  "request.expirationTime" */ _4), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffff)
                    /// @src 11:17068:17149  "request.expirationTime != NO_EXPIRATION_TIME && request.expirationTime <= _time()"
                    let expr_1 := /** @src 11:17068:17112  "request.expirationTime != NO_EXPIRATION_TIME" */ iszero(iszero(cleaned))
                    /// @src 11:17068:17149  "request.expirationTime != NO_EXPIRATION_TIME && request.expirationTime <= _time()"
                    if expr_1
                    {
                        expr_1 := /** @src 11:17116:17149  "request.expirationTime <= _time()" */ iszero(gt(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ cleaned, and(/** @src 11:29893:29908  "block.timestamp" */ timestamp(), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffff)))
                    }
                    /// @src 11:17064:17214  "if (request.expirationTime != NO_EXPIRATION_TIME && request.expirationTime <= _time()) {..."
                    if expr_1
                    {
                        /// @src 11:17176:17199  "InvalidExpirationTime()"
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 11:17176:17199  "InvalidExpirationTime()" */ 0x08e8b93700000000000000000000000000000000000000000000000000000000)
                        revert(/** @src -1:-1:-1 */ 0, /** @src 11:16595:16628  "_schemaRegistry.getSchema(schema)" */ 4)
                    }
                    /// @src 11:17336:17380  "!schemaRecord.revocable && request.revocable"
                    let expr_2 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ iszero(/** @src 11:1790:1791  "0" */ mload(/** @src 11:17337:17359  "schemaRecord.revocable" */ add(expr_3901_mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 64)))
                    /// @src 11:17336:17380  "!schemaRecord.revocable && request.revocable"
                    if expr_2
                    {
                        expr_2 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ iszero(iszero(/** @src 11:1790:1791  "0" */ mload(/** @src 11:17363:17380  "request.revocable" */ add(_320_mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 64))))
                    }
                    /// @src 11:17332:17435  "if (!schemaRecord.revocable && request.revocable) {..."
                    if expr_2
                    {
                        /// @src 11:17407:17420  "Irrevocable()"
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 11:17407:17420  "Irrevocable()" */ 0x157bd4c300000000000000000000000000000000000000000000000000000000)
                        revert(/** @src -1:-1:-1 */ 0, /** @src 11:16595:16628  "_schemaRegistry.getSchema(schema)" */ 4)
                    }
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    let _5 := mload(/** @src 11:17584:17598  "request.refUID" */ add(_320_mpos, 96))
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    let cleaned_1 := and(/** @src 16:138:139  "0" */ mload(/** @src 11:17663:17685  "request.expirationTime" */ _4), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffff)
                    let cleaned_2 := and(mload(/** @src 11:17749:17766  "request.recipient" */ _320_mpos), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffff)
                    let cleaned_3 := iszero(iszero(/** @src 11:1790:1791  "0" */ mload(/** @src 11:17831:17848  "request.revocable" */ add(_320_mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 64))))
                    /// @src 11:17872:17884  "request.data"
                    let _354_mpos := mload(add(_320_mpos, 128))
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    let memPtr := mload(64)
                    finalize_allocation_16871(memPtr)
                    mstore(memPtr, /** @src -1:-1:-1 */ 0)
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    mstore(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, /** @src 11:16437:16445  "res.uids" */ 32), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ var_schema)
                    mstore(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 64), and(/** @src 11:29893:29908  "block.timestamp" */ timestamp(), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffff))
                    mstore(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, /** @src 11:17584:17598  "request.refUID" */ 96), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ cleaned_1)
                    mstore(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, /** @src 11:17872:17884  "request.data" */ 128), /** @src -1:-1:-1 */ 0)
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    mstore(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, 160), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _5)
                    mstore(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, 192), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ cleaned_2)
                    mstore(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 224), and(mload(0xa0), 0xffffffffffffffffffffffffffffffffffffffff))
                    mstore(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, 256), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ cleaned_3)
                    mstore(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, 288), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _354_mpos)
                    /// @src 11:18025:18036  "bytes32 uid"
                    let var_uid := /** @src -1:-1:-1 */ 0
                    /// @src 11:18025:18036  "bytes32 uid"
                    var_uid := /** @src -1:-1:-1 */ var_uid
                    /// @src 11:18050:18065  "uint32 bump = 0"
                    let var_bump := /** @src -1:-1:-1 */ 0
                    /// @src 11:18079:18326  "while (true) {..."
                    for { }
                    /** @src 11:18086:18090  "true" */ 0x01
                    /// @src 11:18079:18326  "while (true) {..."
                    { }
                    {
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        let _6 := mload(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, /** @src 11:16437:16445  "res.uids" */ 32))
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        let _7 := mload(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, 192))
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        let _8 := mload(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 224))
                        /// @src 16:138:139  "0"
                        let _9 := mload(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 64))
                        /// @src 16:138:139  "0"
                        let _10 := mload(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, /** @src 11:17584:17598  "request.refUID" */ 96))
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        let cleaned_4 := iszero(iszero(/** @src 11:1790:1791  "0" */ mload(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, 256))))
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        let _11 := mload(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, 160))
                        /// @src 11:27187:27203  "attestation.data"
                        let _mpos := mload(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, 288))
                        /// @src 11:26855:27247  "abi.encodePacked(..."
                        let expr_mpos := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(64)
                        /// @src 11:26855:27247  "abi.encodePacked(..."
                        let _12 := add(expr_mpos, /** @src 11:16437:16445  "res.uids" */ 32)
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        mstore(_12, _6)
                        mstore(add(/** @src 11:26855:27247  "abi.encodePacked(..." */ expr_mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 64), and(shl(/** @src 11:17584:17598  "request.refUID" */ 96, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _7), 0xffffffffffffffffffffffffffffffffffffffff000000000000000000000000))
                        mstore(add(/** @src 11:26855:27247  "abi.encodePacked(..." */ expr_mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 84), and(shl(/** @src 11:17584:17598  "request.refUID" */ 96, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _8), 0xffffffffffffffffffffffffffffffffffffffff000000000000000000000000))
                        mstore(add(/** @src 11:26855:27247  "abi.encodePacked(..." */ expr_mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 104), and(shl(/** @src 11:17482:17899  "Attestation({..." */ 192, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _9), 0xffffffffffffffff000000000000000000000000000000000000000000000000))
                        mstore(add(/** @src 11:26855:27247  "abi.encodePacked(..." */ expr_mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 112), and(shl(/** @src 11:17482:17899  "Attestation({..." */ 192, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _10), 0xffffffffffffffff000000000000000000000000000000000000000000000000))
                        mstore(add(/** @src 11:26855:27247  "abi.encodePacked(..." */ expr_mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 120), shl(248, cleaned_4))
                        mstore(add(/** @src 11:26855:27247  "abi.encodePacked(..." */ expr_mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 121), _11)
                        let length := mload(_mpos)
                        copy_memory_to_memory_with_cleanup(add(_mpos, /** @src 11:16437:16445  "res.uids" */ 32), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ add(/** @src 11:26855:27247  "abi.encodePacked(..." */ expr_mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 153), length)
                        let _13 := add(/** @src 11:26855:27247  "abi.encodePacked(..." */ expr_mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ length)
                        mstore(add(_13, 153), and(shl(224, var_bump), 0xffffffff00000000000000000000000000000000000000000000000000000000))
                        /// @src 11:26855:27247  "abi.encodePacked(..."
                        let _14 := add(sub(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _13, /** @src 11:26855:27247  "abi.encodePacked(..." */ expr_mpos), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 153)
                        /// @src 11:26855:27247  "abi.encodePacked(..."
                        mstore(expr_mpos, add(_14, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe4))
                        finalize_allocation(expr_mpos, add(_14, /** @src 11:16595:16628  "_schemaRegistry.getSchema(schema)" */ 4))
                        /// @src 11:18110:18142  "uid = _getUID(attestation, bump)"
                        var_uid := /** @src 11:26828:27261  "keccak256(..." */ keccak256(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _12, mload(/** @src 11:26828:27261  "keccak256(..." */ expr_mpos))
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ var_uid)
                        mstore(/** @src 11:16437:16445  "res.uids" */ 32, /** @src 11:18086:18090  "true" */ 0x01)
                        /// @src 11:18160:18237  "if (_db[uid].uid == EMPTY_UID) {..."
                        if /** @src 11:18164:18189  "_db[uid].uid == EMPTY_UID" */ iszero(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ sload(keccak256(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 64)))
                        /// @src 11:18160:18237  "if (_db[uid].uid == EMPTY_UID) {..."
                        {
                            /// @src 11:18213:18218  "break"
                            break
                        }
                        /// @src 11:18287:18293  "++bump"
                        var_bump := /** @src 11:1790:1791  "0" */ and(add(/** @src 11:18287:18293  "++bump" */ var_bump, /** @src 11:18086:18090  "true" */ 0x01), /** @src 11:1790:1791  "0" */ 0xffffffff)
                    }
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    mstore(memPtr, var_uid)
                    mstore(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ var_uid)
                    mstore(/** @src 11:16437:16445  "res.uids" */ 32, /** @src 11:18086:18090  "true" */ 0x01)
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    let dataSlot := keccak256(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 64)
                    /// @src 11:1790:1791  "0"
                    sstore(dataSlot, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 11:1790:1791  "0" */ memPtr))
                    sstore(add(dataSlot, /** @src 11:18086:18090  "true" */ 0x01), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, /** @src 11:16437:16445  "res.uids" */ 32)))
                    /// @src 11:1790:1791  "0"
                    let memberSlot := add(dataSlot, 2)
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    sstore(memberSlot, or(and(sload(memberSlot), 0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000), and(and(/** @src 16:138:139  "0" */ mload(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 64)), 0xffffffffffffffff), 0xffffffffffffffff)))
                    /// @src 16:138:139  "0"
                    let _15 := mload(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, /** @src 11:17584:17598  "request.refUID" */ 96))
                    /// @src 11:1790:1791  "0"
                    let _16 := sload(memberSlot)
                    sstore(memberSlot, or(and(_16, 0xffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff), and(shl(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 64, _15), /** @src 11:1790:1791  "0" */ 0xffffffffffffffff0000000000000000)))
                    update_storage_value_offset_uint64_to_uint64(memberSlot, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(/** @src 16:138:139  "0" */ mload(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, /** @src 11:17872:17884  "request.data" */ 128)), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffff))
                    /// @src 11:1790:1791  "0"
                    sstore(add(dataSlot, 3), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, 160)))
                    /// @src 11:1790:1791  "0"
                    let value := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(mload(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, 192)), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffff)
                    /// @src 11:1790:1791  "0"
                    let slot := add(dataSlot, /** @src 11:16595:16628  "_schemaRegistry.getSchema(schema)" */ 4)
                    /// @src 11:1790:1791  "0"
                    sstore(slot, or(and(sload(slot), 0xffffffffffffffffffffffff0000000000000000000000000000000000000000), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(/** @src 11:1790:1791  "0" */ value, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffff)))
                    /// @src 11:1790:1791  "0"
                    let memberSlot_1 := add(dataSlot, 5)
                    sstore(memberSlot_1, or(and(sload(memberSlot_1), 0xffffffffffffffffffffffff0000000000000000000000000000000000000000), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(and(mload(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 224)), 0xffffffffffffffffffffffffffffffffffffffff), 0xffffffffffffffffffffffffffffffffffffffff)))
                    let cleaned_5 := iszero(iszero(/** @src 11:1790:1791  "0" */ mload(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, 256))))
                    /// @src 11:1790:1791  "0"
                    let _17 := sload(memberSlot_1)
                    sstore(memberSlot_1, or(and(_17, 0xffffffffffffffffffffff00ffffffffffffffffffffffffffffffffffffffff), and(shl(/** @src 11:17482:17899  "Attestation({..." */ 160, /** @src 11:1790:1791  "0" */ cleaned_5), 0xff0000000000000000000000000000000000000000)))
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    let _18 := mload(/** @src 11:17482:17899  "Attestation({..." */ add(memPtr, 288))
                    /// @src 11:1790:1791  "0"
                    let newLen := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 11:1790:1791  "0" */ _18)
                    if gt(newLen, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffff)
                    /// @src 11:1790:1791  "0"
                    {
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 35408467139433450592217433187231851964531694900788300625387963629091585785856)
                        mstore(/** @src 11:16595:16628  "_schemaRegistry.getSchema(schema)" */ 4, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0x41)
                        revert(/** @src -1:-1:-1 */ 0, /** @src 11:16595:16628  "_schemaRegistry.getSchema(schema)" */ 36)
                    }
                    /// @src 11:1790:1791  "0"
                    let _19 := extract_byte_array_length(sload(add(dataSlot, 6)))
                    if gt(_19, 31)
                    {
                        if gt(_19, newLen)
                        {
                            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                            mstore(/** @src -1:-1:-1 */ 0, /** @src 11:1790:1791  "0" */ add(dataSlot, 6))
                            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                            let data := keccak256(/** @src -1:-1:-1 */ 0, /** @src 11:16437:16445  "res.uids" */ 32)
                            /// @src 11:1790:1791  "0"
                            let newSlotCount := shr(5, add(newLen, 31))
                            if lt(newLen, /** @src 11:16437:16445  "res.uids" */ 32)
                            /// @src 11:1790:1791  "0"
                            {
                                newSlotCount := /** @src -1:-1:-1 */ 0
                            }
                            /// @src 11:1790:1791  "0"
                            let i := /** @src -1:-1:-1 */ 0
                            /// @src 11:1790:1791  "0"
                            for { }
                            lt(i, sub(shr(5, add(_19, 31)), newSlotCount))
                            {
                                i := add(i, /** @src 11:18086:18090  "true" */ 0x01)
                            }
                            /// @src 11:1790:1791  "0"
                            {
                                sstore(add(add(data, newSlotCount), i), /** @src -1:-1:-1 */ 0)
                            }
                        }
                    }
                    /// @src 11:1790:1791  "0"
                    let srcOffset := /** @src -1:-1:-1 */ 0
                    /// @src 11:1790:1791  "0"
                    srcOffset := /** @src 11:16437:16445  "res.uids" */ 32
                    /// @src 11:1790:1791  "0"
                    switch gt(newLen, 31)
                    case 1 {
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 11:1790:1791  "0" */ add(dataSlot, 6))
                        let dstPtr := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ keccak256(/** @src -1:-1:-1 */ 0, /** @src 11:16437:16445  "res.uids" */ srcOffset)
                        /// @src 11:1790:1791  "0"
                        let i_1 := /** @src -1:-1:-1 */ 0
                        /// @src 11:1790:1791  "0"
                        for { }
                        lt(i_1, and(newLen, /** @src 11:26855:27247  "abi.encodePacked(..." */ 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0))
                        /// @src 11:1790:1791  "0"
                        {
                            i_1 := add(i_1, /** @src 11:16437:16445  "res.uids" */ 32)
                        }
                        /// @src 11:1790:1791  "0"
                        {
                            sstore(dstPtr, mload(add(_18, srcOffset)))
                            dstPtr := add(dstPtr, /** @src 11:18086:18090  "true" */ 0x01)
                            /// @src 11:1790:1791  "0"
                            srcOffset := add(srcOffset, /** @src 11:16437:16445  "res.uids" */ 32)
                        }
                        /// @src 11:1790:1791  "0"
                        if lt(and(newLen, /** @src 11:26855:27247  "abi.encodePacked(..." */ 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0), /** @src 11:1790:1791  "0" */ newLen)
                        {
                            let lastValue := mload(add(_18, srcOffset))
                            sstore(dstPtr, and(lastValue, not(shr(and(shl(3, newLen), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 248), /** @src 11:1790:1791  "0" */ 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff))))
                        }
                        sstore(add(dataSlot, 6), add(shl(/** @src 11:18086:18090  "true" */ 0x01, /** @src 11:1790:1791  "0" */ newLen), /** @src 11:18086:18090  "true" */ 0x01))
                    }
                    default /// @src 11:1790:1791  "0"
                    {
                        let value_1 := /** @src -1:-1:-1 */ 0
                        /// @src 11:1790:1791  "0"
                        if newLen
                        {
                            value_1 := mload(add(_18, srcOffset))
                        }
                        sstore(add(dataSlot, 6), or(and(value_1, not(shr(shl(3, newLen), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff))), shl(/** @src 11:18086:18090  "true" */ 0x01, /** @src 11:1790:1791  "0" */ newLen)))
                    }
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    let _20 := mload(/** @src 11:17584:17598  "request.refUID" */ add(_320_mpos, 96))
                    /// @src 11:18412:18660  "if (request.refUID != 0) {..."
                    if /** @src 11:18416:18435  "request.refUID != 0" */ iszero(iszero(_20))
                    /// @src 11:18412:18660  "if (request.refUID != 0) {..."
                    {
                        /// @src 11:18547:18646  "if (!isAttestationValid(request.refUID)) {..."
                        if /** @src 11:18551:18586  "!isAttestationValid(request.refUID)" */ iszero(/** @src 11:18552:18586  "isAttestationValid(request.refUID)" */ fun_isAttestationValid(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _20))
                        /// @src 11:18547:18646  "if (!isAttestationValid(request.refUID)) {..."
                        {
                            /// @src 11:18617:18627  "NotFound()"
                            mstore(/** @src -1:-1:-1 */ 0, /** @src 11:18617:18627  "NotFound()" */ 0xc5723b5100000000000000000000000000000000000000000000000000000000)
                            revert(/** @src -1:-1:-1 */ 0, /** @src 11:16595:16628  "_schemaRegistry.getSchema(schema)" */ 4)
                        }
                    }
                    /// @src 11:18674:18703  "attestations[i] = attestation"
                    mstore(memory_array_index_access_array_bytes32_dyn_dyn(expr_3922_mpos, var_i), memPtr)
                    pop(memory_array_index_access_array_bytes32_dyn_dyn(expr_3922_mpos, var_i))
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    mstore(/** @src 11:18717:18742  "values[i] = request.value" */ memory_array_index_access_array_bytes32_dyn_dyn(expr_3933_mpos, var_i), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 11:18729:18742  "request.value" */ add(_320_mpos, /** @src 11:17482:17899  "Attestation({..." */ 160)))
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    mstore(/** @src 11:18757:18774  "res.uids[i] = uid" */ memory_array_index_access_array_bytes32_dyn_dyn(/** @src 11:18757:18765  "res.uids" */ mload(/** @src 11:16437:16445  "res.uids" */ add(mload(0x80), 32)), /** @src 11:18757:18774  "res.uids[i] = uid" */ var_i), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ var_uid)
                    let cleaned_6 := and(mload(/** @src 11:18803:18820  "request.recipient" */ _320_mpos), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffff)
                    /// @src 11:18794:18844  "Attested(request.recipient, attester, uid, schema)"
                    let _21 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(64)
                    mstore(_21, var_uid)
                    /// @src 11:18794:18844  "Attested(request.recipient, attester, uid, schema)"
                    log4(_21, /** @src 11:16437:16445  "res.uids" */ 32, /** @src 11:18794:18844  "Attested(request.recipient, attester, uid, schema)" */ 0x8bf46bf4cfd674fa735a3d63ec1c9ad4153f033c290341f3a588b75685141b35, cleaned_6, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(mload(0xa0), 0xffffffffffffffffffffffffffffffffffffffff), /** @src 11:18794:18844  "Attested(request.recipient, attester, uid, schema)" */ var_schema)
                    /// @src 11:18887:18890  "++i"
                    var_i := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ add(/** @src 11:18887:18890  "++i" */ var_i, /** @src 11:18086:18090  "true" */ 0x01)
                }
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                mstore(mload(0x80), /** @src 11:18941:19026  "_resolveAttestations(schemaRecord, attestations, values, false, availableValue, last)" */ fun__resolveAttestations(expr_3901_mpos, expr_3922_mpos, expr_3933_mpos, var_availableValue, var_last))
                /// @src 11:19037:19047  "return res"
                var_mpos := mload(0x80)
            }
            /// @ast-id 4704 @src 11:28080:28723  "function _mergeUIDs(bytes32[][] memory uidLists, uint256 uidsCount) private pure returns (bytes32[] memory) {..."
            function fun_mergeUIDs(var_uidLists_mpos, var_uidsCount) -> var_4636_mpos
            {
                /// @src 11:28222:28246  "new bytes32[](uidsCount)"
                let expr_4647_mpos := allocate_and_zero_memory_array_array_bytes32_dyn(var_uidsCount)
                /// @src 11:28257:28281  "uint256 currentIndex = 0"
                let var_currentIndex := /** @src 11:28280:28281  "0" */ 0x00
                /// @src 11:28296:28309  "uint256 i = 0"
                let var_i := /** @src 11:28280:28281  "0" */ 0x00
                /// @src 11:28291:28695  "for (uint256 i = 0; i < uidLists.length; ) {..."
                for { }
                /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 1
                /// @src 11:28296:28309  "uint256 i = 0"
                { }
                {
                    /// @src 11:28311:28330  "i < uidLists.length"
                    if iszero(lt(var_i, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 11:28315:28330  "uidLists.length" */ var_uidLists_mpos)))
                    /// @src 11:28311:28330  "i < uidLists.length"
                    { break }
                    /// @src 11:28379:28390  "uidLists[i]"
                    let _429_mpos := mload(memory_array_index_access_array_bytes32_dyn_dyn(var_uidLists_mpos, var_i))
                    /// @src 11:28409:28422  "uint256 j = 0"
                    let var_j := /** @src 11:28280:28281  "0" */ 0x00
                    /// @src 11:28404:28626  "for (uint256 j = 0; j < currentUids.length; ) {..."
                    for { }
                    /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 1
                    /// @src 11:28409:28422  "uint256 j = 0"
                    { }
                    {
                        /// @src 11:28424:28446  "j < currentUids.length"
                        if iszero(lt(var_j, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 11:28428:28446  "currentUids.length" */ _429_mpos)))
                        /// @src 11:28424:28446  "j < currentUids.length"
                        { break }
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        mstore(/** @src 11:28468:28503  "uids[currentIndex] = currentUids[j]" */ memory_array_index_access_array_bytes32_dyn_dyn(expr_4647_mpos, var_currentIndex), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 11:28489:28503  "currentUids[j]" */ memory_array_index_access_array_bytes32_dyn_dyn(_429_mpos, var_j)))
                        /// @src 11:28554:28557  "++j"
                        var_j := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ add(/** @src 11:28554:28557  "++j" */ var_j, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 1)
                        /// @src 11:28579:28593  "++currentIndex"
                        var_currentIndex := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ add(/** @src 11:28579:28593  "++currentIndex" */ var_currentIndex, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 1)
                    }
                    /// @src 11:28667:28670  "++i"
                    var_i := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ add(/** @src 11:28667:28670  "++i" */ var_i, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 1)
                }
                /// @src 11:28705:28716  "return uids"
                var_4636_mpos := expr_4647_mpos
            }
            /// @ast-id 4281 @src 11:19550:21744  "function _revoke(..."
            function fun_revoke(var_schema, var_data_mpos, var_revoker, var_availableValue) -> var
            {
                /// @src 11:19864:19897  "_schemaRegistry.getSchema(schema)"
                let _1 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(64)
                /// @src 11:19864:19897  "_schemaRegistry.getSchema(schema)"
                mstore(_1, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xa2ea7c6e00000000000000000000000000000000000000000000000000000000)
                mstore(/** @src 11:19864:19897  "_schemaRegistry.getSchema(schema)" */ add(_1, 4), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ var_schema)
                /// @src 11:19864:19897  "_schemaRegistry.getSchema(schema)"
                let _2 := staticcall(gas(), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(/** @src 11:19864:19879  "_schemaRegistry" */ loadimmutable("3001"), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffff), /** @src 11:19864:19897  "_schemaRegistry.getSchema(schema)" */ _1, 36, _1, /** @src -1:-1:-1 */ 0)
                /// @src 11:19864:19897  "_schemaRegistry.getSchema(schema)"
                if iszero(_2)
                {
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    let pos := mload(64)
                    returndatacopy(pos, /** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ returndatasize())
                    revert(pos, returndatasize())
                }
                /// @src 11:19864:19897  "_schemaRegistry.getSchema(schema)"
                let expr_mpos := /** @src -1:-1:-1 */ 0
                /// @src 11:19864:19897  "_schemaRegistry.getSchema(schema)"
                if _2
                {
                    let _3 := returndatasize()
                    returndatacopy(_1, /** @src -1:-1:-1 */ 0, /** @src 11:19864:19897  "_schemaRegistry.getSchema(schema)" */ _3)
                    finalize_allocation(_1, _3)
                    expr_mpos := abi_decode_struct_SchemaRecord_fromMemory(_1, add(_1, _3))
                }
                /// @src 11:19907:19989  "if (schemaRecord.uid == EMPTY_UID) {..."
                if /** @src 11:19911:19940  "schemaRecord.uid == EMPTY_UID" */ iszero(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 11:19911:19927  "schemaRecord.uid" */ expr_mpos))
                /// @src 11:19907:19989  "if (schemaRecord.uid == EMPTY_UID) {..."
                {
                    /// @src 11:19963:19978  "InvalidSchema()"
                    mstore(/** @src -1:-1:-1 */ 0, /** @src 11:19963:19978  "InvalidSchema()" */ 0xbf37b20e00000000000000000000000000000000000000000000000000000000)
                    revert(/** @src -1:-1:-1 */ 0, /** @src 11:19864:19897  "_schemaRegistry.getSchema(schema)" */ 4)
                }
                /// @src 11:20016:20027  "data.length"
                let expr := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 11:20016:20027  "data.length" */ var_data_mpos)
                /// @src 11:20073:20098  "new Attestation[](length)"
                let expr_mpos_1 := allocate_and_zero_memory_array_array_struct_Attestation_dyn(expr)
                /// @src 11:20134:20155  "new uint256[](length)"
                let expr_mpos_2 := allocate_and_zero_memory_array_array_bytes32_dyn(expr)
                /// @src 11:20171:20184  "uint256 i = 0"
                let var_i := /** @src -1:-1:-1 */ 0
                /// @src 11:21383:21390  "_time()"
                let expr_1 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(/** @src 11:29893:29908  "block.timestamp" */ timestamp(), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffff)
                /// @src 11:20166:21636  "for (uint256 i = 0; i < length; ) {..."
                for { }
                /** @src 11:20186:20196  "i < length" */ lt(var_i, expr)
                /// @src 11:20171:20184  "uint256 i = 0"
                { }
                {
                    /// @src 11:20253:20260  "data[i]"
                    let _mpos := mload(memory_array_index_access_array_bytes32_dyn_dyn(var_data_mpos, var_i))
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    mstore(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 11:20313:20324  "request.uid" */ _mpos))
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    mstore(32, /** @src 11:9338:9339  "1" */ 0x01)
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    let dataSlot := keccak256(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 64)
                    /// @src 11:20426:20510  "if (attestation.uid == EMPTY_UID) {..."
                    if /** @src 11:20430:20458  "attestation.uid == EMPTY_UID" */ iszero(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ sload(/** @src 11:20430:20445  "attestation.uid" */ dataSlot))
                    /// @src 11:20426:20510  "if (attestation.uid == EMPTY_UID) {..."
                    {
                        /// @src 11:20485:20495  "NotFound()"
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 11:20485:20495  "NotFound()" */ 0xc5723b5100000000000000000000000000000000000000000000000000000000)
                        revert(/** @src -1:-1:-1 */ 0, /** @src 11:19864:19897  "_schemaRegistry.getSchema(schema)" */ 4)
                    }
                    /// @src 11:20600:20618  "attestation.schema"
                    let _4 := add(dataSlot, /** @src 11:9338:9339  "1" */ 0x01)
                    /// @src 11:20596:20685  "if (attestation.schema != schema) {..."
                    if /** @src 11:20600:20628  "attestation.schema != schema" */ iszero(eq(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ sload(/** @src 11:20600:20618  "attestation.schema" */ _4), /** @src 11:20600:20628  "attestation.schema != schema" */ var_schema))
                    /// @src 11:20596:20685  "if (attestation.schema != schema) {..."
                    {
                        /// @src 11:20655:20670  "InvalidSchema()"
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 11:20655:20670  "InvalidSchema()" */ 0xbf37b20e00000000000000000000000000000000000000000000000000000000)
                        revert(/** @src -1:-1:-1 */ 0, /** @src 11:19864:19897  "_schemaRegistry.getSchema(schema)" */ 4)
                    }
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    let _5 := sload(/** @src 11:20778:20798  "attestation.attester" */ add(dataSlot, 5))
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    let _6 := and(/** @src 11:20778:20809  "attestation.attester != revoker" */ var_revoker, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffff)
                    /// @src 11:20774:20865  "if (attestation.attester != revoker) {..."
                    if /** @src 11:20778:20809  "attestation.attester != revoker" */ iszero(eq(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(_5, 0xffffffffffffffffffffffffffffffffffffffff), _6))
                    /// @src 11:20774:20865  "if (attestation.attester != revoker) {..."
                    {
                        /// @src 11:20836:20850  "AccessDenied()"
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 11:20836:20850  "AccessDenied()" */ 0x4ca8886700000000000000000000000000000000000000000000000000000000)
                        revert(/** @src -1:-1:-1 */ 0, /** @src 11:19864:19897  "_schemaRegistry.getSchema(schema)" */ 4)
                    }
                    /// @src 11:21071:21152  "if (!attestation.revocable) {..."
                    if /** @src 11:21075:21097  "!attestation.revocable" */ iszero(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(shr(160, _5), 0xff))
                    /// @src 11:21071:21152  "if (!attestation.revocable) {..."
                    {
                        /// @src 11:21124:21137  "Irrevocable()"
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 11:21124:21137  "Irrevocable()" */ 0x157bd4c300000000000000000000000000000000000000000000000000000000)
                        revert(/** @src -1:-1:-1 */ 0, /** @src 11:19864:19897  "_schemaRegistry.getSchema(schema)" */ 4)
                    }
                    /// @src 11:21252:21278  "attestation.revocationTime"
                    let _7 := add(dataSlot, 2)
                    /// @src 11:21248:21341  "if (attestation.revocationTime != 0) {..."
                    if /** @src 11:21252:21283  "attestation.revocationTime != 0" */ iszero(iszero(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(shr(128, sload(/** @src 11:21252:21278  "attestation.revocationTime" */ _7)), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffff)))
                    /// @src 11:21248:21341  "if (attestation.revocationTime != 0) {..."
                    {
                        /// @src 11:21310:21326  "AlreadyRevoked()"
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 11:21310:21326  "AlreadyRevoked()" */ 0x905e710700000000000000000000000000000000000000000000000000000000)
                        revert(/** @src -1:-1:-1 */ 0, /** @src 11:19864:19897  "_schemaRegistry.getSchema(schema)" */ 4)
                    }
                    /// @src 11:21354:21390  "attestation.revocationTime = _time()"
                    update_storage_value_offset_uint64_to_uint64(_7, expr_1)
                    /// @src 11:21405:21434  "attestations[i] = attestation"
                    mstore(memory_array_index_access_array_bytes32_dyn_dyn(expr_mpos_1, var_i), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ read_from_storage_reference_type_struct_Attestation(/** @src 11:21405:21434  "attestations[i] = attestation" */ dataSlot))
                    pop(memory_array_index_access_array_bytes32_dyn_dyn(expr_mpos_1, var_i))
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    mstore(/** @src 11:21448:21473  "values[i] = request.value" */ memory_array_index_access_array_bytes32_dyn_dyn(expr_mpos_2, var_i), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 11:21460:21473  "request.value" */ add(_mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 32)))
                    let cleaned := and(sload(/** @src 11:21501:21522  "attestation.recipient" */ add(dataSlot, /** @src 11:19864:19897  "_schemaRegistry.getSchema(schema)" */ 4)), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffff)
                    let _8 := mload(/** @src 11:21533:21544  "request.uid" */ _mpos)
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    let _9 := sload(/** @src 11:21546:21564  "attestation.schema" */ _4)
                    /// @src 11:21493:21565  "Revoked(attestation.recipient, revoker, request.uid, attestation.schema)"
                    let _10 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(64)
                    mstore(_10, _8)
                    /// @src 11:21493:21565  "Revoked(attestation.recipient, revoker, request.uid, attestation.schema)"
                    log4(_10, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 32, /** @src 11:21493:21565  "Revoked(attestation.recipient, revoker, request.uid, attestation.schema)" */ 0xf930a6e2523c9cc298691873087a740550b8fc85a0680830414c148ed927f615, cleaned, _6, _9)
                    /// @src 11:21608:21611  "++i"
                    var_i := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ add(/** @src 11:21608:21611  "++i" */ var_i, /** @src 11:9338:9339  "1" */ 0x01)
                }
                /// @src 11:21646:21737  "return _resolveAttestations(schemaRecord, attestations, values, true, availableValue, last)"
                var := /** @src 11:21653:21737  "_resolveAttestations(schemaRecord, attestations, values, true, availableValue, last)" */ fun_resolveAttestations(expr_mpos, expr_mpos_1, expr_mpos_2, var_availableValue, /** @src 11:9338:9339  "1" */ 0x01)
            }
            /// @ast-id 4281 @src 11:19550:21744  "function _revoke(..."
            function fun__revoke(var_schema, var_data_4113_mpos, var_revoker, var_availableValue, var_last) -> var
            {
                /// @src 11:19864:19897  "_schemaRegistry.getSchema(schema)"
                let _1 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(64)
                /// @src 11:19864:19897  "_schemaRegistry.getSchema(schema)"
                mstore(_1, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xa2ea7c6e00000000000000000000000000000000000000000000000000000000)
                mstore(/** @src 11:19864:19897  "_schemaRegistry.getSchema(schema)" */ add(_1, 4), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ var_schema)
                /// @src 11:19864:19897  "_schemaRegistry.getSchema(schema)"
                let _2 := staticcall(gas(), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(/** @src 11:19864:19879  "_schemaRegistry" */ loadimmutable("3001"), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffff), /** @src 11:19864:19897  "_schemaRegistry.getSchema(schema)" */ _1, 36, _1, /** @src -1:-1:-1 */ 0)
                /// @src 11:19864:19897  "_schemaRegistry.getSchema(schema)"
                if iszero(_2)
                {
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    let pos := mload(64)
                    returndatacopy(pos, /** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ returndatasize())
                    revert(pos, returndatasize())
                }
                /// @src 11:19864:19897  "_schemaRegistry.getSchema(schema)"
                let expr_mpos := /** @src -1:-1:-1 */ 0
                /// @src 11:19864:19897  "_schemaRegistry.getSchema(schema)"
                if _2
                {
                    let _3 := returndatasize()
                    returndatacopy(_1, /** @src -1:-1:-1 */ 0, /** @src 11:19864:19897  "_schemaRegistry.getSchema(schema)" */ _3)
                    finalize_allocation(_1, _3)
                    expr_mpos := abi_decode_struct_SchemaRecord_fromMemory(_1, add(_1, _3))
                }
                /// @src 11:19907:19989  "if (schemaRecord.uid == EMPTY_UID) {..."
                if /** @src 11:19911:19940  "schemaRecord.uid == EMPTY_UID" */ iszero(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 11:19911:19927  "schemaRecord.uid" */ expr_mpos))
                /// @src 11:19907:19989  "if (schemaRecord.uid == EMPTY_UID) {..."
                {
                    /// @src 11:19963:19978  "InvalidSchema()"
                    mstore(/** @src -1:-1:-1 */ 0, /** @src 11:19963:19978  "InvalidSchema()" */ 0xbf37b20e00000000000000000000000000000000000000000000000000000000)
                    revert(/** @src -1:-1:-1 */ 0, /** @src 11:19864:19897  "_schemaRegistry.getSchema(schema)" */ 4)
                }
                /// @src 11:20016:20027  "data.length"
                let expr := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 11:20016:20027  "data.length" */ var_data_4113_mpos)
                /// @src 11:20073:20098  "new Attestation[](length)"
                let expr_4156_mpos := allocate_and_zero_memory_array_array_struct_Attestation_dyn(expr)
                /// @src 11:20134:20155  "new uint256[](length)"
                let expr_4167_mpos := allocate_and_zero_memory_array_array_bytes32_dyn(expr)
                /// @src 11:20171:20184  "uint256 i = 0"
                let var_i := /** @src -1:-1:-1 */ 0
                /// @src 11:20166:21636  "for (uint256 i = 0; i < length; ) {..."
                for { }
                /** @src 11:20186:20196  "i < length" */ lt(var_i, expr)
                /// @src 11:20171:20184  "uint256 i = 0"
                { }
                {
                    /// @src 11:20253:20260  "data[i]"
                    let _464_mpos := mload(memory_array_index_access_array_bytes32_dyn_dyn(var_data_4113_mpos, var_i))
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    mstore(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 11:20313:20324  "request.uid" */ _464_mpos))
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    mstore(32, /** @src 11:20309:20312  "_db" */ 0x01)
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    let dataSlot := keccak256(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 64)
                    /// @src 11:20426:20510  "if (attestation.uid == EMPTY_UID) {..."
                    if /** @src 11:20430:20458  "attestation.uid == EMPTY_UID" */ iszero(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ sload(/** @src 11:20430:20445  "attestation.uid" */ dataSlot))
                    /// @src 11:20426:20510  "if (attestation.uid == EMPTY_UID) {..."
                    {
                        /// @src 11:20485:20495  "NotFound()"
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 11:20485:20495  "NotFound()" */ 0xc5723b5100000000000000000000000000000000000000000000000000000000)
                        revert(/** @src -1:-1:-1 */ 0, /** @src 11:19864:19897  "_schemaRegistry.getSchema(schema)" */ 4)
                    }
                    /// @src 11:20596:20685  "if (attestation.schema != schema) {..."
                    if /** @src 11:20600:20628  "attestation.schema != schema" */ iszero(eq(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ sload(/** @src 11:20600:20618  "attestation.schema" */ add(dataSlot, /** @src 11:20309:20312  "_db" */ 0x01)), /** @src 11:20600:20628  "attestation.schema != schema" */ var_schema))
                    /// @src 11:20596:20685  "if (attestation.schema != schema) {..."
                    {
                        /// @src 11:20655:20670  "InvalidSchema()"
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 11:20655:20670  "InvalidSchema()" */ 0xbf37b20e00000000000000000000000000000000000000000000000000000000)
                        revert(/** @src -1:-1:-1 */ 0, /** @src 11:19864:19897  "_schemaRegistry.getSchema(schema)" */ 4)
                    }
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    let _4 := sload(/** @src 11:20778:20798  "attestation.attester" */ add(dataSlot, 5))
                    /// @src 11:20774:20865  "if (attestation.attester != revoker) {..."
                    if /** @src 11:20778:20809  "attestation.attester != revoker" */ iszero(eq(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(_4, 0xffffffffffffffffffffffffffffffffffffffff), and(/** @src 11:20778:20809  "attestation.attester != revoker" */ var_revoker, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffff)))
                    /// @src 11:20774:20865  "if (attestation.attester != revoker) {..."
                    {
                        /// @src 11:20836:20850  "AccessDenied()"
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 11:20836:20850  "AccessDenied()" */ 0x4ca8886700000000000000000000000000000000000000000000000000000000)
                        revert(/** @src -1:-1:-1 */ 0, /** @src 11:19864:19897  "_schemaRegistry.getSchema(schema)" */ 4)
                    }
                    /// @src 11:21071:21152  "if (!attestation.revocable) {..."
                    if /** @src 11:21075:21097  "!attestation.revocable" */ iszero(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(shr(160, _4), 0xff))
                    /// @src 11:21071:21152  "if (!attestation.revocable) {..."
                    {
                        /// @src 11:21124:21137  "Irrevocable()"
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 11:21124:21137  "Irrevocable()" */ 0x157bd4c300000000000000000000000000000000000000000000000000000000)
                        revert(/** @src -1:-1:-1 */ 0, /** @src 11:19864:19897  "_schemaRegistry.getSchema(schema)" */ 4)
                    }
                    /// @src 11:21252:21278  "attestation.revocationTime"
                    let _5 := add(dataSlot, 2)
                    /// @src 11:21248:21341  "if (attestation.revocationTime != 0) {..."
                    if /** @src 11:21252:21283  "attestation.revocationTime != 0" */ iszero(iszero(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(shr(128, sload(/** @src 11:21252:21278  "attestation.revocationTime" */ _5)), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffff)))
                    /// @src 11:21248:21341  "if (attestation.revocationTime != 0) {..."
                    {
                        /// @src 11:21310:21326  "AlreadyRevoked()"
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 11:21310:21326  "AlreadyRevoked()" */ 0x905e710700000000000000000000000000000000000000000000000000000000)
                        revert(/** @src -1:-1:-1 */ 0, /** @src 11:19864:19897  "_schemaRegistry.getSchema(schema)" */ 4)
                    }
                    /// @src 11:21354:21390  "attestation.revocationTime = _time()"
                    update_storage_value_offset_uint64_to_uint64(_5, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(/** @src 11:29893:29908  "block.timestamp" */ timestamp(), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffff))
                    /// @src 11:21405:21434  "attestations[i] = attestation"
                    mstore(memory_array_index_access_array_bytes32_dyn_dyn(expr_4156_mpos, var_i), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ read_from_storage_reference_type_struct_Attestation(/** @src 11:21405:21434  "attestations[i] = attestation" */ dataSlot))
                    pop(memory_array_index_access_array_bytes32_dyn_dyn(expr_4156_mpos, var_i))
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    mstore(/** @src 11:21448:21473  "values[i] = request.value" */ memory_array_index_access_array_bytes32_dyn_dyn(expr_4167_mpos, var_i), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 11:21460:21473  "request.value" */ add(_464_mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 32)))
                    let cleaned := and(sload(/** @src 11:21501:21522  "attestation.recipient" */ add(dataSlot, /** @src 11:19864:19897  "_schemaRegistry.getSchema(schema)" */ 4)), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffff)
                    let _6 := mload(/** @src 11:21533:21544  "request.uid" */ _464_mpos)
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    let _7 := sload(/** @src 11:20600:20618  "attestation.schema" */ add(dataSlot, /** @src 11:20309:20312  "_db" */ 0x01))
                    /// @src 11:21493:21565  "Revoked(attestation.recipient, revoker, request.uid, attestation.schema)"
                    let _8 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(64)
                    mstore(_8, _6)
                    /// @src 11:21493:21565  "Revoked(attestation.recipient, revoker, request.uid, attestation.schema)"
                    log4(_8, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 32, /** @src 11:21493:21565  "Revoked(attestation.recipient, revoker, request.uid, attestation.schema)" */ 0xf930a6e2523c9cc298691873087a740550b8fc85a0680830414c148ed927f615, cleaned, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(/** @src 11:20778:20809  "attestation.attester != revoker" */ var_revoker, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffff), /** @src 11:21493:21565  "Revoked(attestation.recipient, revoker, request.uid, attestation.schema)" */ _7)
                    /// @src 11:21608:21611  "++i"
                    var_i := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ add(/** @src 11:21608:21611  "++i" */ var_i, /** @src 11:20309:20312  "_db" */ 0x01)
                }
                /// @src 11:21646:21737  "return _resolveAttestations(schemaRecord, attestations, values, true, availableValue, last)"
                var := /** @src 11:21653:21737  "_resolveAttestations(schemaRecord, attestations, values, true, availableValue, last)" */ fun_resolveAttestations(expr_mpos, expr_4156_mpos, expr_4167_mpos, var_availableValue, var_last)
            }
            /// @ast-id 4734 @src 11:28879:29104  "function _timestamp(bytes32 data, uint64 time) private {..."
            function fun_timestamp(var_data, var_time)
            {
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                mstore(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ var_data)
                mstore(0x20, /** @src 11:28948:28959  "_timestamps" */ 0x02)
                /// @src 11:28944:29024  "if (_timestamps[data] != 0) {..."
                if /** @src 11:28948:28970  "_timestamps[data] != 0" */ iszero(iszero(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(sload(keccak256(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0x40)), 0xffffffffffffffff)))
                /// @src 11:28944:29024  "if (_timestamps[data] != 0) {..."
                {
                    /// @src 11:28993:29013  "AlreadyTimestamped()"
                    mstore(/** @src -1:-1:-1 */ 0, /** @src 11:28993:29013  "AlreadyTimestamped()" */ 0x2e26794600000000000000000000000000000000000000000000000000000000)
                    revert(/** @src -1:-1:-1 */ 0, /** @src 11:28993:29013  "AlreadyTimestamped()" */ 4)
                }
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                mstore(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ var_data)
                mstore(0x20, /** @src 11:28948:28959  "_timestamps" */ 0x02)
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                let dataSlot := keccak256(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0x40)
                sstore(/** @src 11:29034:29051  "_timestamps[data]" */ dataSlot, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ or(and(sload(/** @src 11:29034:29051  "_timestamps[data]" */ dataSlot), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000), and(/** @src 11:29034:29058  "_timestamps[data] = time" */ var_time, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffff)))
                /// @src 11:29074:29097  "Timestamped(data, time)"
                log3(/** @src -1:-1:-1 */ 0, 0, /** @src 11:29074:29097  "Timestamped(data, time)" */ 0x5aafceeb1c7ad58e4a84898bdee37c02c0fc46e7d24e6b60e8209449f183459f, var_data, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(/** @src 11:29074:29097  "Timestamped(data, time)" */ var_time, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffff))
            }
            /// @ast-id 4947 @src 12:2588:3466  "function _verifyAttest(DelegatedAttestationRequest memory request) internal {..."
            function fun_verifyAttest(var_request_mpos)
            {
                /// @src 12:2711:2723  "request.data"
                let _552_mpos := mload(add(var_request_mpos, 32))
                /// @src 12:2768:2785  "request.signature"
                let _555_mpos := mload(add(var_request_mpos, 64))
                /// @src 12:2859:2875  "request.attester"
                let _1 := add(var_request_mpos, 96)
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                mstore(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(mload(/** @src 12:2859:2875  "request.attester" */ _1), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                mstore(/** @src 12:2711:2723  "request.data" */ 32, /** @src -1:-1:-1 */ 0)
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                let dataSlot := keccak256(/** @src -1:-1:-1 */ 0, /** @src 12:2768:2785  "request.signature" */ 64)
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                let _2 := sload(/** @src 12:2851:2878  "_nonces[request.attester]++" */ dataSlot)
                /// @src 11:1790:1791  "0"
                sstore(dataSlot, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ add(/** @src 12:2851:2878  "_nonces[request.attester]++" */ _2, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 1))
                let _3 := mload(/** @src 12:3042:3056  "request.schema" */ var_request_mpos)
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                let cleaned := and(mload(/** @src 12:3078:3092  "data.recipient" */ _552_mpos), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffff)
                let cleaned_1 := and(/** @src 16:138:139  "0" */ mload(/** @src 12:3114:3133  "data.expirationTime" */ add(_552_mpos, /** @src 12:2711:2723  "request.data" */ 32)), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffff)
                let cleaned_2 := iszero(iszero(/** @src 11:1790:1791  "0" */ mload(/** @src 12:3155:3169  "data.revocable" */ add(_552_mpos, /** @src 12:2768:2785  "request.signature" */ 64))))
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                let _4 := mload(/** @src 12:3191:3202  "data.refUID" */ add(_552_mpos, /** @src 12:2859:2875  "request.attester" */ 96))
                /// @src 12:3234:3243  "data.data"
                let _581_mpos := mload(add(_552_mpos, 128))
                /// @src 12:3224:3244  "keccak256(data.data)"
                let expr := keccak256(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ add(/** @src 12:3224:3244  "keccak256(data.data)" */ _581_mpos, /** @src 12:2711:2723  "request.data" */ 32), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 12:3224:3244  "keccak256(data.data)" */ _581_mpos))
                /// @src 12:2973:3289  "abi.encode(..."
                let expr_4924_mpos := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 12:2768:2785  "request.signature" */ 64)
                /// @src 12:2973:3289  "abi.encode(..."
                let _5 := add(expr_4924_mpos, /** @src 12:2711:2723  "request.data" */ 32)
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                mstore(_5, /** @src 12:921:987  "0xdbfdf8dc2b135c26253e00d5b6cbe6f20457e003fd526d97cea183883570de61" */ 0xdbfdf8dc2b135c26253e00d5b6cbe6f20457e003fd526d97cea183883570de61)
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                mstore(add(/** @src 12:2973:3289  "abi.encode(..." */ expr_4924_mpos, /** @src 12:2768:2785  "request.signature" */ 64), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _3)
                mstore(add(/** @src 12:2973:3289  "abi.encode(..." */ expr_4924_mpos, /** @src 12:2859:2875  "request.attester" */ 96), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ cleaned)
                mstore(add(/** @src 12:2973:3289  "abi.encode(..." */ expr_4924_mpos, /** @src 12:3234:3243  "data.data" */ 128), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ cleaned_1)
                mstore(add(/** @src 12:2973:3289  "abi.encode(..." */ expr_4924_mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 160), cleaned_2)
                mstore(add(/** @src 12:2973:3289  "abi.encode(..." */ expr_4924_mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 192), _4)
                mstore(add(/** @src 12:2973:3289  "abi.encode(..." */ expr_4924_mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 224), expr)
                mstore(add(/** @src 12:2973:3289  "abi.encode(..." */ expr_4924_mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 256), _2)
                /// @src 12:2973:3289  "abi.encode(..."
                mstore(expr_4924_mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 256)
                /// @src 12:2973:3289  "abi.encode(..."
                finalize_allocation(expr_4924_mpos, 288)
                /// @src 12:2916:3313  "_hashTypedDataV4(..."
                let expr_1 := fun_hashTypedDataV4(/** @src 12:2946:3303  "keccak256(..." */ keccak256(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _5, mload(/** @src 12:2946:3303  "keccak256(..." */ expr_4924_mpos)))
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                let cleaned_3 := and(mload(/** @src 12:3350:3361  "signature.v" */ _555_mpos), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xff)
                let _6 := mload(/** @src 12:3363:3374  "signature.r" */ add(_555_mpos, /** @src 12:2711:2723  "request.data" */ 32))
                /// @src 8:6880:6905  "tryRecover(hash, v, r, s)"
                let expr_component, expr_component_1 := fun_tryRecover(expr_1, cleaned_3, _6, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 12:3376:3387  "signature.s" */ add(_555_mpos, /** @src 12:2768:2785  "request.signature" */ 64)))
                /// @src 8:6927:6932  "error"
                fun_throwError(expr_component_1)
                /// @src 12:3324:3460  "if (ECDSA.recover(digest, signature.v, signature.r, signature.s) != request.attester) {..."
                if /** @src 12:3328:3408  "ECDSA.recover(digest, signature.v, signature.r, signature.s) != request.attester" */ iszero(eq(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(/** @src 12:3328:3408  "ECDSA.recover(digest, signature.v, signature.r, signature.s) != request.attester" */ expr_component, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffff), and(mload(/** @src 12:3392:3408  "request.attester" */ _1), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffff)))
                /// @src 12:3324:3460  "if (ECDSA.recover(digest, signature.v, signature.r, signature.s) != request.attester) {..."
                {
                    /// @src 12:3431:3449  "InvalidSignature()"
                    mstore(/** @src -1:-1:-1 */ 0, /** @src 12:3431:3449  "InvalidSignature()" */ 0x8baa579f00000000000000000000000000000000000000000000000000000000)
                    revert(/** @src -1:-1:-1 */ 0, /** @src 12:3431:3449  "InvalidSignature()" */ 4)
                }
            }
            /// @ast-id 5013 @src 12:3619:4185  "function _verifyRevoke(DelegatedRevocationRequest memory request) internal {..."
            function fun_verifyRevoke(var_request_4951_mpos)
            {
                /// @src 12:3740:3752  "request.data"
                let _mpos := mload(add(var_request_4951_mpos, 32))
                /// @src 12:3797:3814  "request.signature"
                let _605_mpos := mload(add(var_request_4951_mpos, 64))
                /// @src 12:3888:3903  "request.revoker"
                let _1 := add(var_request_4951_mpos, 96)
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                mstore(/** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(mload(/** @src 12:3888:3903  "request.revoker" */ _1), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                mstore(/** @src 12:3740:3752  "request.data" */ 32, /** @src -1:-1:-1 */ 0)
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                let dataSlot := keccak256(/** @src -1:-1:-1 */ 0, /** @src 12:3797:3814  "request.signature" */ 64)
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                let _2 := sload(/** @src 12:3880:3906  "_nonces[request.revoker]++" */ dataSlot)
                /// @src 11:1790:1791  "0"
                sstore(dataSlot, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ add(/** @src 12:3880:3906  "_nonces[request.revoker]++" */ _2, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 1))
                let _3 := mload(/** @src 12:3999:4013  "request.schema" */ var_request_4951_mpos)
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                let _4 := mload(/** @src 12:4015:4023  "data.uid" */ _mpos)
                /// @src 12:3971:4031  "abi.encode(REVOKE_TYPEHASH, request.schema, data.uid, nonce)"
                let expr_4990_mpos := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 12:3797:3814  "request.signature" */ 64)
                /// @src 12:3971:4031  "abi.encode(REVOKE_TYPEHASH, request.schema, data.uid, nonce)"
                let _5 := add(expr_4990_mpos, /** @src 12:3740:3752  "request.data" */ 32)
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                mstore(_5, /** @src 12:1202:1268  "0xa98d02348410c9c76735e0d0bb1396f4015ac2bb9615f9c2611d19d7a8a99650" */ 0xa98d02348410c9c76735e0d0bb1396f4015ac2bb9615f9c2611d19d7a8a99650)
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                mstore(add(/** @src 12:3971:4031  "abi.encode(REVOKE_TYPEHASH, request.schema, data.uid, nonce)" */ expr_4990_mpos, /** @src 12:3797:3814  "request.signature" */ 64), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _3)
                mstore(add(/** @src 12:3971:4031  "abi.encode(REVOKE_TYPEHASH, request.schema, data.uid, nonce)" */ expr_4990_mpos, /** @src 12:3888:3903  "request.revoker" */ 96), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _4)
                mstore(add(/** @src 12:3971:4031  "abi.encode(REVOKE_TYPEHASH, request.schema, data.uid, nonce)" */ expr_4990_mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 128), _2)
                /// @src 12:3971:4031  "abi.encode(REVOKE_TYPEHASH, request.schema, data.uid, nonce)"
                mstore(expr_4990_mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 128)
                /// @src 12:3971:4031  "abi.encode(REVOKE_TYPEHASH, request.schema, data.uid, nonce)"
                finalize_allocation(expr_4990_mpos, 160)
                /// @src 12:3944:4033  "_hashTypedDataV4(keccak256(abi.encode(REVOKE_TYPEHASH, request.schema, data.uid, nonce)))"
                let expr := fun_hashTypedDataV4(/** @src 12:3961:4032  "keccak256(abi.encode(REVOKE_TYPEHASH, request.schema, data.uid, nonce))" */ keccak256(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _5, mload(/** @src 12:3961:4032  "keccak256(abi.encode(REVOKE_TYPEHASH, request.schema, data.uid, nonce))" */ expr_4990_mpos)))
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                let cleaned := and(mload(/** @src 12:4070:4081  "signature.v" */ _605_mpos), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xff)
                let _6 := mload(/** @src 12:4083:4094  "signature.r" */ add(_605_mpos, /** @src 12:3740:3752  "request.data" */ 32))
                /// @src 8:6880:6905  "tryRecover(hash, v, r, s)"
                let expr_component, expr_component_1 := fun_tryRecover(expr, cleaned, _6, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 12:4096:4107  "signature.s" */ add(_605_mpos, /** @src 12:3797:3814  "request.signature" */ 64)))
                /// @src 8:6927:6932  "error"
                fun_throwError(expr_component_1)
                /// @src 12:4044:4179  "if (ECDSA.recover(digest, signature.v, signature.r, signature.s) != request.revoker) {..."
                if /** @src 12:4048:4127  "ECDSA.recover(digest, signature.v, signature.r, signature.s) != request.revoker" */ iszero(eq(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(/** @src 12:4048:4127  "ECDSA.recover(digest, signature.v, signature.r, signature.s) != request.revoker" */ expr_component, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffff), and(mload(/** @src 12:4112:4127  "request.revoker" */ _1), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffff)))
                /// @src 12:4044:4179  "if (ECDSA.recover(digest, signature.v, signature.r, signature.s) != request.revoker) {..."
                {
                    /// @src 12:4150:4168  "InvalidSignature()"
                    mstore(/** @src -1:-1:-1 */ 0, /** @src 12:4150:4168  "InvalidSignature()" */ 0x8baa579f00000000000000000000000000000000000000000000000000000000)
                    revert(/** @src -1:-1:-1 */ 0, /** @src 12:4150:4168  "InvalidSignature()" */ 4)
                }
            }
            /// @ast-id 2004 @src 9:3152:3460  "function _domainSeparatorV4() internal view returns (bytes32) {..."
            function fun_domainSeparatorV4() -> var
            {
                /// @src 9:3205:3212  "bytes32"
                var := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0
                /// @src 9:3228:3294  "address(this) == _CACHED_THIS && block.chainid == _CACHED_CHAIN_ID"
                let expr := /** @src 9:3228:3257  "address(this) == _CACHED_THIS" */ eq(/** @src 9:3236:3240  "this" */ address(), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(/** @src 9:3245:3257  "_CACHED_THIS" */ loadimmutable("1904"), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                /// @src 9:3228:3294  "address(this) == _CACHED_THIS && block.chainid == _CACHED_CHAIN_ID"
                if expr
                {
                    expr := /** @src 9:3261:3294  "block.chainid == _CACHED_CHAIN_ID" */ eq(/** @src 9:3261:3274  "block.chainid" */ chainid(), /** @src 9:3278:3294  "_CACHED_CHAIN_ID" */ loadimmutable("1902"))
                }
                /// @src 9:3224:3454  "if (address(this) == _CACHED_THIS && block.chainid == _CACHED_CHAIN_ID) {..."
                switch expr
                case 0 {
                    /// @src 9:3642:3715  "abi.encode(typeHash, nameHash, versionHash, block.chainid, address(this))"
                    let expr_mpos := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(64)
                    /// @src 9:3642:3715  "abi.encode(typeHash, nameHash, versionHash, block.chainid, address(this))"
                    let _1 := add(expr_mpos, 0x20)
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    mstore(_1, /** @src 9:3401:3411  "_TYPE_HASH" */ loadimmutable("1910"))
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    mstore(add(/** @src 9:3642:3715  "abi.encode(typeHash, nameHash, versionHash, block.chainid, address(this))" */ expr_mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 64), /** @src 9:3413:3425  "_HASHED_NAME" */ loadimmutable("1906"))
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    mstore(add(/** @src 9:3642:3715  "abi.encode(typeHash, nameHash, versionHash, block.chainid, address(this))" */ expr_mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 96), /** @src 9:3427:3442  "_HASHED_VERSION" */ loadimmutable("1908"))
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    mstore(add(/** @src 9:3642:3715  "abi.encode(typeHash, nameHash, versionHash, block.chainid, address(this))" */ expr_mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 128), /** @src 9:3686:3699  "block.chainid" */ chainid())
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    mstore(add(/** @src 9:3642:3715  "abi.encode(typeHash, nameHash, versionHash, block.chainid, address(this))" */ expr_mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 160), /** @src 9:3236:3240  "this" */ address())
                    /// @src 9:3642:3715  "abi.encode(typeHash, nameHash, versionHash, block.chainid, address(this))"
                    mstore(expr_mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 160)
                    /// @src 9:3642:3715  "abi.encode(typeHash, nameHash, versionHash, block.chainid, address(this))"
                    finalize_allocation(expr_mpos, 192)
                    /// @src 9:3372:3443  "return _buildDomainSeparator(_TYPE_HASH, _HASHED_NAME, _HASHED_VERSION)"
                    var := /** @src 9:3632:3716  "keccak256(abi.encode(typeHash, nameHash, versionHash, block.chainid, address(this)))" */ keccak256(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _1, mload(/** @src 9:3632:3716  "keccak256(abi.encode(typeHash, nameHash, versionHash, block.chainid, address(this)))" */ expr_mpos))
                    /// @src 9:3372:3443  "return _buildDomainSeparator(_TYPE_HASH, _HASHED_NAME, _HASHED_VERSION)"
                    leave
                }
                default /// @src 9:3224:3454  "if (address(this) == _CACHED_THIS && block.chainid == _CACHED_CHAIN_ID) {..."
                {
                    /// @src 9:3310:3341  "return _CACHED_DOMAIN_SEPARATOR"
                    var := /** @src 9:3317:3341  "_CACHED_DOMAIN_SEPARATOR" */ loadimmutable("1900")
                    /// @src 9:3310:3341  "return _CACHED_DOMAIN_SEPARATOR"
                    leave
                }
            }
            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
            function abi_encode_array_struct_Attestation_dyn_array_uint256_dyn(headStart, value0, value1) -> tail
            {
                let tail_1 := add(headStart, 64)
                mstore(headStart, 64)
                let pos := tail_1
                let length := mload(value0)
                mstore(tail_1, length)
                pos := add(headStart, 96)
                let tail_2 := add(add(headStart, shl(5, length)), 96)
                let srcPtr := add(value0, 0x20)
                let i := 0
                for { } lt(i, length) { i := add(i, 1) }
                {
                    mstore(pos, add(sub(tail_2, headStart), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa0))
                    tail_2 := abi_encode_struct_Attestation(mload(srcPtr), tail_2)
                    srcPtr := add(srcPtr, 0x20)
                    pos := add(pos, 0x20)
                }
                mstore(add(headStart, 0x20), sub(tail_2, headStart))
                let pos_1 := tail_2
                let length_1 := mload(value1)
                mstore(tail_2, length_1)
                pos_1 := add(tail_2, 0x20)
                let srcPtr_1 := add(value1, 0x20)
                let i_1 := 0
                for { } lt(i_1, length_1) { i_1 := add(i_1, 1) }
                {
                    mstore(pos_1, mload(srcPtr_1))
                    pos_1 := add(pos_1, 0x20)
                    srcPtr_1 := add(srcPtr_1, 0x20)
                }
                tail := pos_1
            }
            /// @ast-id 4569 @src 11:24364:26469  "function _resolveAttestations(..."
            function fun__resolveAttestations(var_schemaRecord_mpos, var_attestations_mpos, var_values_mpos, var_availableValue, var_last) -> var
            {
                /// @ast-id 4569
                let var_isRevocation := /** @src -1:-1:-1 */ 0
                /// @src 11:24613:24620  "uint256"
                var := /** @src -1:-1:-1 */ var_isRevocation
                /// @src 11:24649:24668  "attestations.length"
                let expr := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 11:24649:24668  "attestations.length" */ var_attestations_mpos)
                /// @src 11:24678:24824  "if (length == 1) {..."
                if /** @src 11:24682:24693  "length == 1" */ eq(expr, /** @src 11:24692:24693  "1" */ 0x01)
                /// @src 11:24678:24824  "if (length == 1) {..."
                {
                    /// @src 11:24750:24765  "attestations[0]"
                    let _mpos := mload(memory_array_index_access_array_array_bytes32_dyn_dyn(var_attestations_mpos))
                    /// @src 11:24709:24813  "return _resolveAttestation(schemaRecord, attestations[0], values[0], isRevocation, availableValue, last)"
                    var := /** @src 11:24716:24813  "_resolveAttestation(schemaRecord, attestations[0], values[0], isRevocation, availableValue, last)" */ fun_resolveAttestation(var_schemaRecord_mpos, _mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 11:24767:24776  "values[0]" */ memory_array_index_access_array_array_bytes32_dyn_dyn(var_values_mpos)), /** @src -1:-1:-1 */ var_isRevocation, /** @src 11:24716:24813  "_resolveAttestation(schemaRecord, attestations[0], values[0], isRevocation, availableValue, last)" */ var_availableValue, var_last)
                    /// @src 11:24709:24813  "return _resolveAttestation(schemaRecord, attestations[0], values[0], isRevocation, availableValue, last)"
                    leave
                }
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                let cleaned := and(mload(/** @src 11:24861:24882  "schemaRecord.resolver" */ add(var_schemaRecord_mpos, 32)), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffff)
                /// @src 11:24892:25271  "if (address(resolver) == address(0)) {..."
                if /** @src 11:24896:24927  "address(resolver) == address(0)" */ iszero(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ cleaned)
                /// @src 11:24892:25271  "if (address(resolver) == address(0)) {..."
                {
                    /// @src 11:25025:25038  "uint256 i = 0"
                    let var_i := /** @src -1:-1:-1 */ var_isRevocation
                    /// @src 11:25020:25238  "for (uint256 i = 0; i < length; ) {..."
                    for { }
                    /** @src 11:25040:25050  "i < length" */ lt(var_i, expr)
                    /// @src 11:25025:25038  "uint256 i = 0"
                    { }
                    {
                        /// @src 11:25072:25152  "if (values[i] != 0) {..."
                        if /** @src 11:25076:25090  "values[i] != 0" */ iszero(iszero(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 11:25076:25085  "values[i]" */ memory_array_index_access_array_bytes32_dyn_dyn(var_values_mpos, var_i))))
                        /// @src 11:25072:25152  "if (values[i] != 0) {..."
                        {
                            /// @src 11:25121:25133  "NotPayable()"
                            mstore(/** @src -1:-1:-1 */ var_isRevocation, /** @src 11:25121:25133  "NotPayable()" */ 0x1574f9f300000000000000000000000000000000000000000000000000000000)
                            revert(/** @src -1:-1:-1 */ var_isRevocation, /** @src 11:25121:25133  "NotPayable()" */ 4)
                        }
                        /// @src 11:25202:25205  "++i"
                        var_i := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ add(/** @src 11:25202:25205  "++i" */ var_i, /** @src 11:24692:24693  "1" */ 0x01)
                    }
                    /// @src 11:25252:25260  "return 0"
                    var := /** @src -1:-1:-1 */ var_isRevocation
                    /// @src 11:25252:25260  "return 0"
                    leave
                }
                /// @src 11:25281:25307  "uint256 totalUsedValue = 0"
                let var_totalUsedValue := /** @src -1:-1:-1 */ var_isRevocation
                /// @src 11:25323:25336  "uint256 i = 0"
                let var_i_1 := /** @src -1:-1:-1 */ var_isRevocation
                /// @src 11:25318:26044  "for (uint256 i = 0; i < length; ) {..."
                for { }
                /** @src 11:25338:25348  "i < length" */ lt(var_i_1, expr)
                /// @src 11:25323:25336  "uint256 i = 0"
                { }
                {
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    let _1 := mload(/** @src 11:25382:25391  "values[i]" */ memory_array_index_access_array_bytes32_dyn_dyn(var_values_mpos, var_i_1))
                    /// @src 11:25504:25539  "value != 0 && !resolver.isPayable()"
                    let expr_1 := /** @src 11:25504:25514  "value != 0" */ iszero(iszero(_1))
                    /// @src 11:25504:25539  "value != 0 && !resolver.isPayable()"
                    if expr_1
                    {
                        /// @src 11:25519:25539  "resolver.isPayable()"
                        let _2 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(64)
                        /// @src 11:25519:25539  "resolver.isPayable()"
                        mstore(_2, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xce46e04600000000000000000000000000000000000000000000000000000000)
                        /// @src 11:25519:25539  "resolver.isPayable()"
                        let _3 := staticcall(gas(), cleaned, _2, 4, _2, /** @src 11:24861:24882  "schemaRecord.resolver" */ 32)
                        /// @src 11:25519:25539  "resolver.isPayable()"
                        if iszero(_3)
                        {
                            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                            let pos := mload(64)
                            returndatacopy(pos, /** @src -1:-1:-1 */ var_isRevocation, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ returndatasize())
                            revert(pos, returndatasize())
                        }
                        /// @src 11:25519:25539  "resolver.isPayable()"
                        let expr_2 := /** @src -1:-1:-1 */ var_isRevocation
                        /// @src 11:25519:25539  "resolver.isPayable()"
                        if _3
                        {
                            let _4 := /** @src 11:24861:24882  "schemaRecord.resolver" */ 32
                            /// @src 11:25519:25539  "resolver.isPayable()"
                            if gt(/** @src 11:24861:24882  "schemaRecord.resolver" */ _4, /** @src 11:25519:25539  "resolver.isPayable()" */ returndatasize()) { _4 := returndatasize() }
                            finalize_allocation(_2, _4)
                            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                            if slt(sub(/** @src 11:25519:25539  "resolver.isPayable()" */ add(_2, _4), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _2), /** @src 11:24861:24882  "schemaRecord.resolver" */ 32)
                            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                            {
                                revert(/** @src -1:-1:-1 */ var_isRevocation, var_isRevocation)
                            }
                            /// @src 11:25519:25539  "resolver.isPayable()"
                            expr_2 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ abi_decode_bool_fromMemory(_2)
                        }
                        /// @src 11:25504:25539  "value != 0 && !resolver.isPayable()"
                        expr_1 := /** @src 11:25518:25539  "!resolver.isPayable()" */ iszero(expr_2)
                    }
                    /// @src 11:25500:25593  "if (value != 0 && !resolver.isPayable()) {..."
                    if expr_1
                    {
                        /// @src 11:25566:25578  "NotPayable()"
                        mstore(/** @src -1:-1:-1 */ var_isRevocation, /** @src 11:25566:25578  "NotPayable()" */ 0x1574f9f300000000000000000000000000000000000000000000000000000000)
                        revert(/** @src -1:-1:-1 */ var_isRevocation, /** @src 11:25566:25578  "NotPayable()" */ 4)
                    }
                    /// @src 11:25697:25784  "if (value > availableValue) {..."
                    if /** @src 11:25701:25723  "value > availableValue" */ gt(_1, var_availableValue)
                    /// @src 11:25697:25784  "if (value > availableValue) {..."
                    {
                        /// @src 11:25750:25769  "InsufficientValue()"
                        mstore(/** @src -1:-1:-1 */ var_isRevocation, /** @src 11:25750:25769  "InsufficientValue()" */ 0x1101129400000000000000000000000000000000000000000000000000000000)
                        revert(/** @src -1:-1:-1 */ var_isRevocation, /** @src 11:25750:25769  "InsufficientValue()" */ 4)
                    }
                    /// @src 11:25933:25956  "availableValue -= value"
                    var_availableValue := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ sub(/** @src 11:25933:25956  "availableValue -= value" */ var_availableValue, _1)
                    /// @src 11:25974:25997  "totalUsedValue += value"
                    var_totalUsedValue := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ add(/** @src 11:25974:25997  "totalUsedValue += value" */ var_totalUsedValue, _1)
                    /// @src 11:26016:26019  "++i"
                    var_i_1 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ add(/** @src 11:26016:26019  "++i" */ var_i_1, /** @src 11:24692:24693  "1" */ 0x01)
                }
                /// @src 11:26054:26363  "if (isRevocation) {..."
                var_isRevocation := /** @src -1:-1:-1 */ var_isRevocation
                /// @src 11:26241:26308  "resolver.multiAttest{ value: totalUsedValue }(attestations, values)"
                let _5 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(64)
                /// @src 11:26241:26308  "resolver.multiAttest{ value: totalUsedValue }(attestations, values)"
                mstore(_5, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0x91db0b7e00000000000000000000000000000000000000000000000000000000)
                /// @src 11:26241:26308  "resolver.multiAttest{ value: totalUsedValue }(attestations, values)"
                let _6 := call(gas(), cleaned, var_totalUsedValue, _5, sub(abi_encode_array_struct_Attestation_dyn_array_uint256_dyn(add(_5, 4), var_attestations_mpos, var_values_mpos), _5), _5, /** @src 11:24861:24882  "schemaRecord.resolver" */ 32)
                /// @src 11:26241:26308  "resolver.multiAttest{ value: totalUsedValue }(attestations, values)"
                if iszero(_6)
                {
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    let pos_1 := mload(64)
                    returndatacopy(pos_1, /** @src 11:26054:26363  "if (isRevocation) {..." */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ returndatasize())
                    revert(pos_1, returndatasize())
                }
                /// @src 11:26241:26308  "resolver.multiAttest{ value: totalUsedValue }(attestations, values)"
                let expr_3 := /** @src 11:26054:26363  "if (isRevocation) {..." */ 0
                /// @src 11:26241:26308  "resolver.multiAttest{ value: totalUsedValue }(attestations, values)"
                if _6
                {
                    let _7 := /** @src 11:24861:24882  "schemaRecord.resolver" */ 32
                    /// @src 11:26241:26308  "resolver.multiAttest{ value: totalUsedValue }(attestations, values)"
                    if gt(/** @src 11:24861:24882  "schemaRecord.resolver" */ 32, /** @src 11:26241:26308  "resolver.multiAttest{ value: totalUsedValue }(attestations, values)" */ returndatasize()) { _7 := returndatasize() }
                    finalize_allocation(_5, _7)
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    if slt(sub(/** @src 11:26241:26308  "resolver.multiAttest{ value: totalUsedValue }(attestations, values)" */ add(_5, _7), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _5), /** @src 11:24861:24882  "schemaRecord.resolver" */ 32)
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    {
                        revert(/** @src 11:26054:26363  "if (isRevocation) {..." */ 0, 0)
                    }
                    /// @src 11:26241:26308  "resolver.multiAttest{ value: totalUsedValue }(attestations, values)"
                    expr_3 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ abi_decode_bool_fromMemory(_5)
                }
                /// @src 11:26236:26363  "if (!resolver.multiAttest{ value: totalUsedValue }(attestations, values)) {..."
                if /** @src 11:26240:26308  "!resolver.multiAttest{ value: totalUsedValue }(attestations, values)" */ iszero(expr_3)
                /// @src 11:26236:26363  "if (!resolver.multiAttest{ value: totalUsedValue }(attestations, values)) {..."
                {
                    /// @src 11:26331:26352  "InvalidAttestations()"
                    mstore(/** @src 11:26054:26363  "if (isRevocation) {..." */ 0, /** @src 11:26331:26352  "InvalidAttestations()" */ 0xe8bee83900000000000000000000000000000000000000000000000000000000)
                    revert(/** @src 11:26054:26363  "if (isRevocation) {..." */ 0, /** @src 11:26241:26308  "resolver.multiAttest{ value: totalUsedValue }(attestations, values)" */ 4)
                }
                /// @src 11:26373:26431  "if (last) {..."
                if var_last
                {
                    /// @src 11:26405:26419  "availableValue"
                    fun_refund(var_availableValue)
                }
                /// @src 11:26441:26462  "return totalUsedValue"
                var := var_totalUsedValue
            }
            /// @ast-id 4569 @src 11:24364:26469  "function _resolveAttestations(..."
            function fun_resolveAttestations(var_schemaRecord_mpos, var_attestations_mpos, var_values_mpos, var_availableValue, var_last) -> var
            {
                /// @src 11:24613:24620  "uint256"
                var := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0
                /// @src 11:24649:24668  "attestations.length"
                let expr := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 11:24649:24668  "attestations.length" */ var_attestations_mpos)
                /// @src 11:24678:24824  "if (length == 1) {..."
                if /** @src 11:24682:24693  "length == 1" */ eq(expr, /** @src 11:20309:20312  "_db" */ 0x01)
                /// @src 11:24678:24824  "if (length == 1) {..."
                {
                    /// @src 11:24750:24765  "attestations[0]"
                    let _mpos := mload(memory_array_index_access_array_array_bytes32_dyn_dyn(var_attestations_mpos))
                    /// @src 11:24709:24813  "return _resolveAttestation(schemaRecord, attestations[0], values[0], isRevocation, availableValue, last)"
                    var := /** @src 11:24716:24813  "_resolveAttestation(schemaRecord, attestations[0], values[0], isRevocation, availableValue, last)" */ fun_resolveAttestation(var_schemaRecord_mpos, _mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 11:24767:24776  "values[0]" */ memory_array_index_access_array_array_bytes32_dyn_dyn(var_values_mpos)), /** @src 11:20309:20312  "_db" */ 0x01, /** @src 11:24716:24813  "_resolveAttestation(schemaRecord, attestations[0], values[0], isRevocation, availableValue, last)" */ var_availableValue, var_last)
                    /// @src 11:24709:24813  "return _resolveAttestation(schemaRecord, attestations[0], values[0], isRevocation, availableValue, last)"
                    leave
                }
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                let cleaned := and(mload(/** @src 11:24861:24882  "schemaRecord.resolver" */ add(var_schemaRecord_mpos, 32)), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffff)
                /// @src 11:24892:25271  "if (address(resolver) == address(0)) {..."
                if /** @src 11:24896:24927  "address(resolver) == address(0)" */ iszero(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ cleaned)
                /// @src 11:24892:25271  "if (address(resolver) == address(0)) {..."
                {
                    /// @src 11:25025:25038  "uint256 i = 0"
                    let var_i := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0
                    /// @src 11:25020:25238  "for (uint256 i = 0; i < length; ) {..."
                    for { }
                    /** @src 11:25040:25050  "i < length" */ lt(var_i, expr)
                    /// @src 11:25025:25038  "uint256 i = 0"
                    { }
                    {
                        /// @src 11:25072:25152  "if (values[i] != 0) {..."
                        if /** @src 11:25076:25090  "values[i] != 0" */ iszero(iszero(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(/** @src 11:25076:25085  "values[i]" */ memory_array_index_access_array_bytes32_dyn_dyn(var_values_mpos, var_i))))
                        /// @src 11:25072:25152  "if (values[i] != 0) {..."
                        {
                            /// @src 11:25121:25133  "NotPayable()"
                            mstore(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0, /** @src 11:25121:25133  "NotPayable()" */ 0x1574f9f300000000000000000000000000000000000000000000000000000000)
                            revert(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0, /** @src 11:25121:25133  "NotPayable()" */ 4)
                        }
                        /// @src 11:25202:25205  "++i"
                        var_i := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ add(/** @src 11:25202:25205  "++i" */ var_i, /** @src 11:20309:20312  "_db" */ 0x01)
                    }
                    /// @src 11:25252:25260  "return 0"
                    var := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0
                    /// @src 11:25252:25260  "return 0"
                    leave
                }
                /// @src 11:25281:25307  "uint256 totalUsedValue = 0"
                let var_totalUsedValue := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0
                /// @src 11:25323:25336  "uint256 i = 0"
                let var_i_1 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0
                /// @src 11:25318:26044  "for (uint256 i = 0; i < length; ) {..."
                for { }
                /** @src 11:25338:25348  "i < length" */ lt(var_i_1, expr)
                /// @src 11:25323:25336  "uint256 i = 0"
                { }
                {
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    let _1 := mload(/** @src 11:25382:25391  "values[i]" */ memory_array_index_access_array_bytes32_dyn_dyn(var_values_mpos, var_i_1))
                    /// @src 11:25504:25539  "value != 0 && !resolver.isPayable()"
                    let expr_1 := /** @src 11:25504:25514  "value != 0" */ iszero(iszero(_1))
                    /// @src 11:25504:25539  "value != 0 && !resolver.isPayable()"
                    if expr_1
                    {
                        /// @src 11:25519:25539  "resolver.isPayable()"
                        let _2 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(64)
                        /// @src 11:25519:25539  "resolver.isPayable()"
                        mstore(_2, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xce46e04600000000000000000000000000000000000000000000000000000000)
                        /// @src 11:25519:25539  "resolver.isPayable()"
                        let _3 := staticcall(gas(), cleaned, _2, 4, _2, /** @src 11:24861:24882  "schemaRecord.resolver" */ 32)
                        /// @src 11:25519:25539  "resolver.isPayable()"
                        if iszero(_3)
                        {
                            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                            let pos := mload(64)
                            returndatacopy(pos, 0, returndatasize())
                            revert(pos, returndatasize())
                        }
                        /// @src 11:25519:25539  "resolver.isPayable()"
                        let expr_2 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0
                        /// @src 11:25519:25539  "resolver.isPayable()"
                        if _3
                        {
                            let _4 := /** @src 11:24861:24882  "schemaRecord.resolver" */ 32
                            /// @src 11:25519:25539  "resolver.isPayable()"
                            if gt(/** @src 11:24861:24882  "schemaRecord.resolver" */ _4, /** @src 11:25519:25539  "resolver.isPayable()" */ returndatasize()) { _4 := returndatasize() }
                            finalize_allocation(_2, _4)
                            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                            if slt(sub(/** @src 11:25519:25539  "resolver.isPayable()" */ add(_2, _4), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _2), /** @src 11:24861:24882  "schemaRecord.resolver" */ 32)
                            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                            { revert(expr_2, expr_2) }
                            /// @src 11:25519:25539  "resolver.isPayable()"
                            expr_2 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ abi_decode_bool_fromMemory(_2)
                        }
                        /// @src 11:25504:25539  "value != 0 && !resolver.isPayable()"
                        expr_1 := /** @src 11:25518:25539  "!resolver.isPayable()" */ iszero(expr_2)
                    }
                    /// @src 11:25500:25593  "if (value != 0 && !resolver.isPayable()) {..."
                    if expr_1
                    {
                        /// @src 11:25566:25578  "NotPayable()"
                        mstore(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0, /** @src 11:25566:25578  "NotPayable()" */ 0x1574f9f300000000000000000000000000000000000000000000000000000000)
                        revert(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0, /** @src 11:25566:25578  "NotPayable()" */ 4)
                    }
                    /// @src 11:25697:25784  "if (value > availableValue) {..."
                    if /** @src 11:25701:25723  "value > availableValue" */ gt(_1, var_availableValue)
                    /// @src 11:25697:25784  "if (value > availableValue) {..."
                    {
                        /// @src 11:25750:25769  "InsufficientValue()"
                        mstore(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0, /** @src 11:25750:25769  "InsufficientValue()" */ 0x1101129400000000000000000000000000000000000000000000000000000000)
                        revert(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0, /** @src 11:25750:25769  "InsufficientValue()" */ 4)
                    }
                    /// @src 11:25933:25956  "availableValue -= value"
                    var_availableValue := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ sub(/** @src 11:25933:25956  "availableValue -= value" */ var_availableValue, _1)
                    /// @src 11:25974:25997  "totalUsedValue += value"
                    var_totalUsedValue := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ add(/** @src 11:25974:25997  "totalUsedValue += value" */ var_totalUsedValue, _1)
                    /// @src 11:26016:26019  "++i"
                    var_i_1 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ add(/** @src 11:26016:26019  "++i" */ var_i_1, /** @src 11:20309:20312  "_db" */ 0x01)
                }
                /// @src 11:26091:26158  "resolver.multiRevoke{ value: totalUsedValue }(attestations, values)"
                let _5 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(64)
                /// @src 11:26091:26158  "resolver.multiRevoke{ value: totalUsedValue }(attestations, values)"
                mstore(_5, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0x88e5b2d900000000000000000000000000000000000000000000000000000000)
                /// @src 11:26091:26158  "resolver.multiRevoke{ value: totalUsedValue }(attestations, values)"
                let _6 := call(gas(), cleaned, var_totalUsedValue, _5, sub(abi_encode_array_struct_Attestation_dyn_array_uint256_dyn(add(_5, 4), var_attestations_mpos, var_values_mpos), _5), _5, /** @src 11:24861:24882  "schemaRecord.resolver" */ 32)
                /// @src 11:26091:26158  "resolver.multiRevoke{ value: totalUsedValue }(attestations, values)"
                if iszero(_6)
                {
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    let pos_1 := mload(64)
                    returndatacopy(pos_1, 0, returndatasize())
                    revert(pos_1, returndatasize())
                }
                /// @src 11:26091:26158  "resolver.multiRevoke{ value: totalUsedValue }(attestations, values)"
                let expr_3 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0
                /// @src 11:26091:26158  "resolver.multiRevoke{ value: totalUsedValue }(attestations, values)"
                if _6
                {
                    let _7 := /** @src 11:24861:24882  "schemaRecord.resolver" */ 32
                    /// @src 11:26091:26158  "resolver.multiRevoke{ value: totalUsedValue }(attestations, values)"
                    if gt(/** @src 11:24861:24882  "schemaRecord.resolver" */ 32, /** @src 11:26091:26158  "resolver.multiRevoke{ value: totalUsedValue }(attestations, values)" */ returndatasize()) { _7 := returndatasize() }
                    finalize_allocation(_5, _7)
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    if slt(sub(/** @src 11:26091:26158  "resolver.multiRevoke{ value: totalUsedValue }(attestations, values)" */ add(_5, _7), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _5), /** @src 11:24861:24882  "schemaRecord.resolver" */ 32)
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    { revert(0, 0) }
                    /// @src 11:26091:26158  "resolver.multiRevoke{ value: totalUsedValue }(attestations, values)"
                    expr_3 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ abi_decode_bool_fromMemory(_5)
                }
                /// @src 11:26086:26220  "if (!resolver.multiRevoke{ value: totalUsedValue }(attestations, values)) {..."
                if /** @src 11:26090:26158  "!resolver.multiRevoke{ value: totalUsedValue }(attestations, values)" */ iszero(expr_3)
                /// @src 11:26086:26220  "if (!resolver.multiRevoke{ value: totalUsedValue }(attestations, values)) {..."
                {
                    /// @src 11:26185:26205  "InvalidRevocations()"
                    mstore(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0, /** @src 11:26185:26205  "InvalidRevocations()" */ 0xbf2f3a8b00000000000000000000000000000000000000000000000000000000)
                    revert(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0, /** @src 11:26091:26158  "resolver.multiRevoke{ value: totalUsedValue }(attestations, values)" */ 4)
                }
                /// @src 11:26373:26431  "if (last) {..."
                if var_last
                {
                    /// @src 11:26405:26419  "availableValue"
                    fun_refund(var_availableValue)
                }
                /// @src 11:26441:26462  "return totalUsedValue"
                var := var_totalUsedValue
            }
            /// @ast-id 2047 @src 9:4348:4513  "function _hashTypedDataV4(bytes32 structHash) internal view virtual returns (bytes32) {..."
            function fun_hashTypedDataV4(var_structHash) -> var
            {
                /// @src 9:4473:4493  "_domainSeparatorV4()"
                let _1 := fun_domainSeparatorV4()
                /// @src 8:8470:8527  "abi.encodePacked(\"\\x19\\x01\", domainSeparator, structHash)"
                let expr_mpos := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(64)
                /// @src 8:8470:8527  "abi.encodePacked(\"\\x19\\x01\", domainSeparator, structHash)"
                let _2 := add(expr_mpos, 0x20)
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                mstore(_2, 0x1901000000000000000000000000000000000000000000000000000000000000)
                mstore(add(/** @src 8:8470:8527  "abi.encodePacked(\"\\x19\\x01\", domainSeparator, structHash)" */ expr_mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 34), _1)
                mstore(add(/** @src 8:8470:8527  "abi.encodePacked(\"\\x19\\x01\", domainSeparator, structHash)" */ expr_mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 66), var_structHash)
                /// @src 8:8470:8527  "abi.encodePacked(\"\\x19\\x01\", domainSeparator, structHash)"
                mstore(expr_mpos, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 66)
                /// @src 8:8470:8527  "abi.encodePacked(\"\\x19\\x01\", domainSeparator, structHash)"
                finalize_allocation(expr_mpos, 98)
                /// @src 9:4444:4506  "return ECDSA.toTypedDataHash(_domainSeparatorV4(), structHash)"
                var := /** @src 8:8460:8528  "keccak256(abi.encodePacked(\"\\x19\\x01\", domainSeparator, structHash))" */ keccak256(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _2, mload(/** @src 8:8460:8528  "keccak256(abi.encodePacked(\"\\x19\\x01\", domainSeparator, structHash))" */ expr_mpos))
            }
            /// @ast-id 4391 @src 11:22357:23749  "function _resolveAttestation(..."
            function fun_resolveAttestation(var_schemaRecord_mpos, var_attestation_mpos, var_value, var_isRevocation, var_availableValue, var_last) -> var
            {
                /// @src 11:22592:22599  "uint256"
                var := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0
                let cleaned := and(mload(/** @src 11:22638:22659  "schemaRecord.resolver" */ add(var_schemaRecord_mpos, 32)), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffff)
                /// @src 11:22669:22898  "if (address(resolver) == address(0)) {..."
                if /** @src 11:22673:22704  "address(resolver) == address(0)" */ iszero(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ cleaned)
                /// @src 11:22669:22898  "if (address(resolver) == address(0)) {..."
                {
                    /// @src 11:22797:22865  "if (value != 0) {..."
                    if /** @src 11:22801:22811  "value != 0" */ iszero(iszero(var_value))
                    /// @src 11:22797:22865  "if (value != 0) {..."
                    {
                        /// @src 11:22838:22850  "NotPayable()"
                        mstore(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0, /** @src 11:22838:22850  "NotPayable()" */ 0x1574f9f300000000000000000000000000000000000000000000000000000000)
                        revert(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0, /** @src 11:22838:22850  "NotPayable()" */ 4)
                    }
                    /// @src 11:22879:22887  "return 0"
                    var := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0
                    /// @src 11:22879:22887  "return 0"
                    leave
                }
                /// @src 11:23002:23037  "value != 0 && !resolver.isPayable()"
                let expr := /** @src 11:23002:23012  "value != 0" */ iszero(iszero(var_value))
                /// @src 11:23002:23037  "value != 0 && !resolver.isPayable()"
                if expr
                {
                    /// @src 11:23017:23037  "resolver.isPayable()"
                    let _1 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(64)
                    /// @src 11:23017:23037  "resolver.isPayable()"
                    mstore(_1, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xce46e04600000000000000000000000000000000000000000000000000000000)
                    /// @src 11:23017:23037  "resolver.isPayable()"
                    let _2 := staticcall(gas(), cleaned, _1, 4, _1, /** @src 11:22638:22659  "schemaRecord.resolver" */ 32)
                    /// @src 11:23017:23037  "resolver.isPayable()"
                    if iszero(_2)
                    {
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        let pos := mload(64)
                        returndatacopy(pos, 0, returndatasize())
                        revert(pos, returndatasize())
                    }
                    /// @src 11:23017:23037  "resolver.isPayable()"
                    let expr_1 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0
                    /// @src 11:23017:23037  "resolver.isPayable()"
                    if _2
                    {
                        let _3 := /** @src 11:22638:22659  "schemaRecord.resolver" */ 32
                        /// @src 11:23017:23037  "resolver.isPayable()"
                        if gt(/** @src 11:22638:22659  "schemaRecord.resolver" */ 32, /** @src 11:23017:23037  "resolver.isPayable()" */ returndatasize()) { _3 := returndatasize() }
                        finalize_allocation(_1, _3)
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        if slt(sub(/** @src 11:23017:23037  "resolver.isPayable()" */ add(_1, _3), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _1), /** @src 11:22638:22659  "schemaRecord.resolver" */ 32)
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        { revert(0, 0) }
                        /// @src 11:23017:23037  "resolver.isPayable()"
                        expr_1 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ abi_decode_bool_fromMemory(_1)
                    }
                    /// @src 11:23002:23037  "value != 0 && !resolver.isPayable()"
                    expr := /** @src 11:23016:23037  "!resolver.isPayable()" */ iszero(expr_1)
                }
                /// @src 11:22998:23083  "if (value != 0 && !resolver.isPayable()) {..."
                if expr
                {
                    /// @src 11:23060:23072  "NotPayable()"
                    mstore(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0, /** @src 11:23060:23072  "NotPayable()" */ 0x1574f9f300000000000000000000000000000000000000000000000000000000)
                    revert(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0, /** @src 11:23060:23072  "NotPayable()" */ 4)
                }
                /// @src 11:23179:23258  "if (value > availableValue) {..."
                if /** @src 11:23183:23205  "value > availableValue" */ gt(var_value, var_availableValue)
                /// @src 11:23179:23258  "if (value > availableValue) {..."
                {
                    /// @src 11:23228:23247  "InsufficientValue()"
                    mstore(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0, /** @src 11:23228:23247  "InsufficientValue()" */ 0x1101129400000000000000000000000000000000000000000000000000000000)
                    revert(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0, /** @src 11:23228:23247  "InsufficientValue()" */ 4)
                }
                /// @src 11:23391:23652  "if (isRevocation) {..."
                switch var_isRevocation
                case 0 {
                    /// @src 11:23554:23598  "resolver.attest{ value: value }(attestation)"
                    let _4 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(64)
                    /// @src 11:23554:23598  "resolver.attest{ value: value }(attestation)"
                    mstore(_4, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xe60c350500000000000000000000000000000000000000000000000000000000)
                    mstore(/** @src 11:23554:23598  "resolver.attest{ value: value }(attestation)" */ add(_4, 4), /** @src 11:22638:22659  "schemaRecord.resolver" */ 32)
                    /// @src 11:23554:23598  "resolver.attest{ value: value }(attestation)"
                    let _5 := call(gas(), cleaned, var_value, _4, sub(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ abi_encode_struct_Attestation(var_attestation_mpos, add(/** @src 11:23554:23598  "resolver.attest{ value: value }(attestation)" */ _4, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 36)), /** @src 11:23554:23598  "resolver.attest{ value: value }(attestation)" */ _4), _4, /** @src 11:22638:22659  "schemaRecord.resolver" */ 32)
                    /// @src 11:23554:23598  "resolver.attest{ value: value }(attestation)"
                    if iszero(_5)
                    {
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        let pos_1 := mload(64)
                        returndatacopy(pos_1, 0, returndatasize())
                        revert(pos_1, returndatasize())
                    }
                    /// @src 11:23554:23598  "resolver.attest{ value: value }(attestation)"
                    let expr_2 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0
                    /// @src 11:23554:23598  "resolver.attest{ value: value }(attestation)"
                    if _5
                    {
                        let _6 := /** @src 11:22638:22659  "schemaRecord.resolver" */ 32
                        /// @src 11:23554:23598  "resolver.attest{ value: value }(attestation)"
                        if gt(/** @src 11:22638:22659  "schemaRecord.resolver" */ 32, /** @src 11:23554:23598  "resolver.attest{ value: value }(attestation)" */ returndatasize()) { _6 := returndatasize() }
                        finalize_allocation(_4, _6)
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        if slt(sub(/** @src 11:23554:23598  "resolver.attest{ value: value }(attestation)" */ add(_4, _6), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _4), /** @src 11:22638:22659  "schemaRecord.resolver" */ 32)
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        { revert(0, 0) }
                        /// @src 11:23554:23598  "resolver.attest{ value: value }(attestation)"
                        expr_2 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ abi_decode_bool_fromMemory(_4)
                    }
                    /// @src 11:23549:23652  "if (!resolver.attest{ value: value }(attestation)) {..."
                    if /** @src 11:23553:23598  "!resolver.attest{ value: value }(attestation)" */ iszero(expr_2)
                    /// @src 11:23549:23652  "if (!resolver.attest{ value: value }(attestation)) {..."
                    {
                        /// @src 11:23621:23641  "InvalidAttestation()"
                        mstore(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0, /** @src 11:23621:23641  "InvalidAttestation()" */ 0xbd8ba84d00000000000000000000000000000000000000000000000000000000)
                        revert(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0, /** @src 11:23554:23598  "resolver.attest{ value: value }(attestation)" */ 4)
                    }
                }
                default /// @src 11:23391:23652  "if (isRevocation) {..."
                {
                    /// @src 11:23428:23472  "resolver.revoke{ value: value }(attestation)"
                    let _7 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(64)
                    /// @src 11:23428:23472  "resolver.revoke{ value: value }(attestation)"
                    mstore(_7, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xe49617e100000000000000000000000000000000000000000000000000000000)
                    mstore(/** @src 11:23428:23472  "resolver.revoke{ value: value }(attestation)" */ add(_7, 4), /** @src 11:22638:22659  "schemaRecord.resolver" */ 32)
                    /// @src 11:23428:23472  "resolver.revoke{ value: value }(attestation)"
                    let _8 := call(gas(), cleaned, var_value, _7, sub(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ abi_encode_struct_Attestation(var_attestation_mpos, add(/** @src 11:23428:23472  "resolver.revoke{ value: value }(attestation)" */ _7, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 36)), /** @src 11:23428:23472  "resolver.revoke{ value: value }(attestation)" */ _7), _7, /** @src 11:22638:22659  "schemaRecord.resolver" */ 32)
                    /// @src 11:23428:23472  "resolver.revoke{ value: value }(attestation)"
                    if iszero(_8)
                    {
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        let pos_2 := mload(64)
                        returndatacopy(pos_2, 0, returndatasize())
                        revert(pos_2, returndatasize())
                    }
                    /// @src 11:23428:23472  "resolver.revoke{ value: value }(attestation)"
                    let expr_3 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0
                    /// @src 11:23428:23472  "resolver.revoke{ value: value }(attestation)"
                    if _8
                    {
                        let _9 := /** @src 11:22638:22659  "schemaRecord.resolver" */ 32
                        /// @src 11:23428:23472  "resolver.revoke{ value: value }(attestation)"
                        if gt(/** @src 11:22638:22659  "schemaRecord.resolver" */ 32, /** @src 11:23428:23472  "resolver.revoke{ value: value }(attestation)" */ returndatasize()) { _9 := returndatasize() }
                        finalize_allocation(_7, _9)
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        if slt(sub(/** @src 11:23428:23472  "resolver.revoke{ value: value }(attestation)" */ add(_7, _9), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ _7), /** @src 11:22638:22659  "schemaRecord.resolver" */ 32)
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        { revert(0, 0) }
                        /// @src 11:23428:23472  "resolver.revoke{ value: value }(attestation)"
                        expr_3 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ abi_decode_bool_fromMemory(_7)
                    }
                    /// @src 11:23423:23533  "if (!resolver.revoke{ value: value }(attestation)) {..."
                    if /** @src 11:23427:23472  "!resolver.revoke{ value: value }(attestation)" */ iszero(expr_3)
                    /// @src 11:23423:23533  "if (!resolver.revoke{ value: value }(attestation)) {..."
                    {
                        /// @src 11:23499:23518  "InvalidRevocation()"
                        mstore(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0, /** @src 11:23499:23518  "InvalidRevocation()" */ 0xccf3bb2700000000000000000000000000000000000000000000000000000000)
                        revert(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0, /** @src 11:23428:23472  "resolver.revoke{ value: value }(attestation)" */ 4)
                    }
                }
                /// @src 11:23662:23720  "if (last) {..."
                if var_last
                {
                    /// @src 11:23694:23708  "availableValue"
                    fun_refund(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ sub(/** @src 11:23347:23370  "availableValue -= value" */ var_availableValue, var_value))
                }
                /// @src 11:23730:23742  "return value"
                var := var_value
            }
            /// @ast-id 4625 @src 11:27444:27859  "function _refund(uint256 remainingValue) private {..."
            function fun_refund(var_remainingValue)
            {
                /// @src 11:27503:27853  "if (remainingValue > 0) {..."
                if /** @src 11:27507:27525  "remainingValue > 0" */ iszero(iszero(var_remainingValue))
                /// @src 11:27503:27853  "if (remainingValue > 0) {..."
                {
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    if /** @src 5:2501:2532  "address(this).balance >= amount" */ lt(/** @src 5:2501:2522  "address(this).balance" */ selfbalance(), /** @src 5:2501:2532  "address(this).balance >= amount" */ var_remainingValue)
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    {
                        let memPtr := mload(64)
                        mstore(memPtr, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                        mstore(add(memPtr, 4), 32)
                        mstore(add(memPtr, 36), 29)
                        mstore(add(memPtr, 68), "Address: insufficient balance")
                        revert(memPtr, 100)
                    }
                    /// @src 5:2596:2629  "recipient.call{value: amount}(\"\")"
                    let expr_component := call(gas(), /** @src 11:27805:27815  "msg.sender" */ caller(), /** @src 5:2596:2629  "recipient.call{value: amount}(\"\")" */ var_remainingValue, /** @src 11:27524:27525  "0" */ 0x00, 0x00, 0x00, 0x00)
                    /// @src 5:2596:2629  "recipient.call{value: amount}(\"\")"
                    let data := /** @src 11:27524:27525  "0" */ 0x00
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    switch returndatasize()
                    case 0 { data := 96 }
                    default {
                        let _1 := returndatasize()
                        let _2 := array_allocation_size_string(_1)
                        let memPtr_1 := mload(64)
                        finalize_allocation(memPtr_1, _2)
                        mstore(memPtr_1, _1)
                        data := memPtr_1
                        returndatacopy(add(memPtr_1, 0x20), /** @src 11:27524:27525  "0" */ 0x00, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ returndatasize())
                    }
                    if iszero(expr_component)
                    {
                        let memPtr_2 := mload(64)
                        mstore(memPtr_2, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                        mstore(add(memPtr_2, 4), 32)
                        mstore(add(memPtr_2, 36), 58)
                        mstore(add(memPtr_2, 68), "Address: unable to send value, r")
                        mstore(add(memPtr_2, 100), "ecipient may have reverted")
                        revert(memPtr_2, 132)
                    }
                }
            }
            /// @ast-id 1801 @src 8:5069:6563  "function tryRecover(..."
            function fun_tryRecover(var_hash, var_v, var_r, var_s) -> var, var_1
            {
                /// @src 8:6102:6263  "if (uint256(s) > 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0) {..."
                if /** @src 8:6106:6185  "uint256(s) > 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0" */ gt(var_s, /** @src 8:6119:6185  "0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0" */ 0x7fffffffffffffffffffffffffffffff5d576e7357a4501ddfe92f46681b20a0)
                /// @src 8:6102:6263  "if (uint256(s) > 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0) {..."
                {
                    /// @src 8:6201:6252  "return (address(0), RecoverError.InvalidSignatureS)"
                    var := /** @src 8:6217:6218  "0" */ 0x00
                    /// @src 8:6201:6252  "return (address(0), RecoverError.InvalidSignatureS)"
                    var_1 := /** @src 8:6221:6251  "RecoverError.InvalidSignatureS" */ 3
                    /// @src 8:6201:6252  "return (address(0), RecoverError.InvalidSignatureS)"
                    leave
                }
                /// @src 8:6374:6398  "ecrecover(hash, v, r, s)"
                let _1 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(64)
                mstore(_1, var_hash)
                mstore(add(_1, 32), and(var_v, 0xff))
                mstore(add(_1, 64), var_r)
                mstore(add(_1, 96), var_s)
                /// @src 8:6374:6398  "ecrecover(hash, v, r, s)"
                mstore(/** @src -1:-1:-1 */ 0, 0)
                /// @src 8:6374:6398  "ecrecover(hash, v, r, s)"
                if iszero(staticcall(gas(), 1, _1, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 128, /** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 32))
                /// @src 8:6374:6398  "ecrecover(hash, v, r, s)"
                {
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    let pos := mload(64)
                    returndatacopy(pos, /** @src -1:-1:-1 */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ returndatasize())
                    revert(pos, returndatasize())
                }
                /// @src 8:6374:6398  "ecrecover(hash, v, r, s)"
                let _2 := mload(/** @src -1:-1:-1 */ 0)
                /// @src 8:6408:6509  "if (signer == address(0)) {..."
                if /** @src 8:6412:6432  "signer == address(0)" */ iszero(/** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ and(/** @src 8:6412:6432  "signer == address(0)" */ _2, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                /// @src 8:6408:6509  "if (signer == address(0)) {..."
                {
                    /// @src 8:6448:6498  "return (address(0), RecoverError.InvalidSignature)"
                    var := /** @src -1:-1:-1 */ 0
                    /// @src 8:6448:6498  "return (address(0), RecoverError.InvalidSignature)"
                    var_1 := /** @src 8:6374:6398  "ecrecover(hash, v, r, s)" */ 1
                    /// @src 8:6448:6498  "return (address(0), RecoverError.InvalidSignature)"
                    leave
                }
                /// @src 8:6519:6556  "return (signer, RecoverError.NoError)"
                var := _2
                var_1 := /** @src -1:-1:-1 */ 0
            }
            /// @ast-id 1587 @src 8:570:1081  "function _throwError(RecoverError error) private pure {..."
            function fun_throwError(var_error)
            {
                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                let _1 := iszero(lt(var_error, 5))
                if _1
                {
                    mstore(/** @src 8:647:667  "RecoverError.NoError" */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 35408467139433450592217433187231851964531694900788300625387963629091585785856)
                    mstore(4, 0x21)
                    revert(/** @src 8:647:667  "RecoverError.NoError" */ 0, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 0x24)
                }
                /// @src 8:634:1075  "if (error == RecoverError.NoError) {..."
                switch /** @src 8:638:667  "error == RecoverError.NoError" */ iszero(var_error)
                case /** @src 8:634:1075  "if (error == RecoverError.NoError) {..." */ 0 {
                    /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                    _1 := /** @src 8:647:667  "RecoverError.NoError" */ 0
                    /// @src 8:730:1075  "if (error == RecoverError.InvalidSignature) {..."
                    switch /** @src 8:734:772  "error == RecoverError.InvalidSignature" */ eq(var_error, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 1)
                    case /** @src 8:730:1075  "if (error == RecoverError.InvalidSignature) {..." */ 0 {
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        _1 := /** @src 8:647:667  "RecoverError.NoError" */ 0
                        /// @src 8:839:1075  "if (error == RecoverError.InvalidSignatureLength) {..."
                        switch /** @src 8:843:887  "error == RecoverError.InvalidSignatureLength" */ eq(var_error, /** @src 8:852:887  "RecoverError.InvalidSignatureLength" */ 2)
                        case /** @src 8:839:1075  "if (error == RecoverError.InvalidSignatureLength) {..." */ 0 {
                            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                            _1 := /** @src 8:647:667  "RecoverError.NoError" */ 0
                            /// @src 8:961:1075  "if (error == RecoverError.InvalidSignatureS) {..."
                            if /** @src 8:965:1004  "error == RecoverError.InvalidSignatureS" */ eq(var_error, /** @src 8:974:1004  "RecoverError.InvalidSignatureS" */ 3)
                            /// @src 8:961:1075  "if (error == RecoverError.InvalidSignatureS) {..."
                            {
                                /// @src 8:1020:1064  "revert(\"ECDSA: invalid signature 's' value\")"
                                let _2 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(64)
                                /// @src 8:1020:1064  "revert(\"ECDSA: invalid signature 's' value\")"
                                mstore(_2, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                                /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                                mstore(/** @src 8:1020:1064  "revert(\"ECDSA: invalid signature 's' value\")" */ add(_2, 4), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 32)
                                mstore(add(/** @src 8:1020:1064  "revert(\"ECDSA: invalid signature 's' value\")" */ _2, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 36), 34)
                                mstore(add(/** @src 8:1020:1064  "revert(\"ECDSA: invalid signature 's' value\")" */ _2, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 68), "ECDSA: invalid signature 's' val")
                                mstore(add(/** @src 8:1020:1064  "revert(\"ECDSA: invalid signature 's' value\")" */ _2, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 100), "ue")
                                /// @src 8:1020:1064  "revert(\"ECDSA: invalid signature 's' value\")"
                                revert(_2, 132)
                            }
                        }
                        default /// @src 8:839:1075  "if (error == RecoverError.InvalidSignatureLength) {..."
                        {
                            /// @src 8:903:944  "revert(\"ECDSA: invalid signature length\")"
                            let _3 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(64)
                            /// @src 8:903:944  "revert(\"ECDSA: invalid signature length\")"
                            mstore(_3, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                            /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                            mstore(/** @src 8:903:944  "revert(\"ECDSA: invalid signature length\")" */ add(_3, 4), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 32)
                            mstore(add(/** @src 8:903:944  "revert(\"ECDSA: invalid signature length\")" */ _3, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 36), 31)
                            mstore(add(/** @src 8:903:944  "revert(\"ECDSA: invalid signature length\")" */ _3, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 68), "ECDSA: invalid signature length")
                            /// @src 8:903:944  "revert(\"ECDSA: invalid signature length\")"
                            revert(_3, 100)
                        }
                    }
                    default /// @src 8:730:1075  "if (error == RecoverError.InvalidSignature) {..."
                    {
                        /// @src 8:788:822  "revert(\"ECDSA: invalid signature\")"
                        let _4 := /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ mload(64)
                        /// @src 8:788:822  "revert(\"ECDSA: invalid signature\")"
                        mstore(_4, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                        /// @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..."
                        mstore(/** @src 8:788:822  "revert(\"ECDSA: invalid signature\")" */ add(_4, 4), /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 32)
                        mstore(add(/** @src 8:788:822  "revert(\"ECDSA: invalid signature\")" */ _4, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 36), 24)
                        mstore(add(/** @src 8:788:822  "revert(\"ECDSA: invalid signature\")" */ _4, /** @src 11:963:29918  "contract EAS is IEAS, EIP712Verifier {..." */ 68), "ECDSA: invalid signature")
                        /// @src 8:788:822  "revert(\"ECDSA: invalid signature\")"
                        revert(_4, 100)
                    }
                }
                default /// @src 8:634:1075  "if (error == RecoverError.NoError) {..."
                {
                    /// @src 8:683:690  "return;"
                    leave
                }
            }
        }
        data ".metadata" hex"a164736f6c6343000820000a"
    }
}

