/// @use-src 0:"src/Midnight.sol", 4:"src/interfaces/IMidnight.sol"
object "Midnight_4129" {
    code {
        {
            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
            let _1 := memoryguard(0x80)
            mstore(64, _1)
            if callvalue() { revert(0, 0) }
            sstore(/** @src 0:14902:14927  "configurator = msg.sender" */ 0x09, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ or(and(sload(/** @src 0:14902:14927  "configurator = msg.sender" */ 0x09), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(sub(shl(160, 1), 1))), /** @src 0:14917:14927  "msg.sender" */ caller()))
            /// @src 0:14942:14975  "EventsLib.Constructor(msg.sender)"
            log2(/** @src -1:-1:-1 */ 0, 0, /** @src 0:14942:14975  "EventsLib.Constructor(msg.sender)" */ 0x385bc760a35ad4b8b2c11c6a4c6d27daa5e72ce47836b34da36a3f1258ec45ec, /** @src 0:14917:14927  "msg.sender" */ caller())
            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
            let _2 := datasize("Midnight_4129_deployed")
            codecopy(_1, dataoffset("Midnight_4129_deployed"), _2)
            return(_1, _2)
        }
    }
    /// @use-src 0:"src/Midnight.sol", 7:"src/libraries/ConstantsLib.sol", 9:"src/libraries/IdLib.sol", 10:"src/libraries/SafeTransferLib.sol", 11:"src/libraries/TickLib.sol", 12:"src/libraries/UtilsLib.sol"
    object "Midnight_4129_deployed" {
        code {
            {
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                mstore(64, memoryguard(0x0340))
                if iszero(lt(calldatasize(), 4))
                {
                    mstore(0x0320, 0)
                    switch shr(224, calldataload(0))
                    case 0x1b14c072 {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), not(3)), 64) { revert(0, 0) }
                        let ret := /** @src 0:54472:54518  "UtilsLib.tGet(LIQUIDATION_LOCK_SLOT, id, user)" */ fun_tGet(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(4), abi_decode_address_44120())
                        let memPos := mload(64)
                        mstore(memPos, iszero(iszero(ret)))
                        return(memPos, 32)
                    }
                    case 0x21559e6b {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), not(3)), 64) { revert(0, 0) }
                        let value0 := abi_decode_address_44122()
                        let value := calldataload(36)
                        if iszero(/** @src 0:20814:20837  "msg.sender == feeSetter" */ eq(/** @src 0:20814:20824  "msg.sender" */ caller(), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(sload(/** @src 0:20828:20837  "feeSetter" */ 0x0a), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff)))
                        {
                            mstore(0, shl(224, 0x7155bb19))
                            revert(0, 4)
                        }
                        /// @src 0:20893:20911  "MAX_CONTINUOUS_FEE"
                        let ret_1 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                        /// @src 7:711:755  "uint32(uint256(0.01e18) / uint256(365 days))"
                        ret_1 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x12e687bf
                        /// @src 7:711:755  "uint32(uint256(0.01e18) / uint256(365 days))"
                        if /** @src 0:20873:20911  "newContinuousFee <= MAX_CONTINUOUS_FEE" */ gt(value, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ ret_1)
                        /// @src 7:711:755  "uint32(uint256(0.01e18) / uint256(365 days))"
                        {
                            mstore(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0, /** @src 7:711:755  "uint32(uint256(0.01e18) / uint256(365 days))" */ shl(224, 0x39ee5d9b))
                            revert(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0, 4)
                        }
                        let _1 := and(value0, 0xffffffffffffffffffffffffffffffffffffffff)
                        mstore(0, _1)
                        mstore(32, /** @src 0:21066:21086  "defaultContinuousFee" */ 0x05)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let dataSlot := keccak256(0, 64)
                        /// @src 7:711:755  "uint32(uint256(0.01e18) / uint256(365 days))"
                        sstore(dataSlot, or(and(sload(dataSlot), not(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffff)), and(/** @src 0:21100:21124  "uint32(newContinuousFee)" */ value, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffff)))
                        /// @src 0:21139:21201  "EventsLib.SetDefaultContinuousFee(loanToken, newContinuousFee)"
                        let _2 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                        mstore(_2, value)
                        /// @src 0:21139:21201  "EventsLib.SetDefaultContinuousFee(loanToken, newContinuousFee)"
                        log2(_2, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32, /** @src 0:21139:21201  "EventsLib.SetDefaultContinuousFee(loanToken, newContinuousFee)" */ 0x57cfac4cdc6c10e16433620e0ab8e58bb0cb760645d7206c700486d8cd3ea769, _1)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        return(0, 0)
                    }
                    case 0x265d32c1 {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), not(3)), 32) { revert(0, 0) }
                        mstore(0, and(abi_decode_address_44122(), 0xffffffffffffffffffffffffffffffffffffffff))
                        mstore(32, /** @src 0:14443:14507  "mapping(address loanToken => uint32) public defaultContinuousFee" */ 5)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let value_1 := and(sload(keccak256(0, 64)), 0xffffffff)
                        let memPos_1 := mload(64)
                        mstore(memPos_1, value_1)
                        return(memPos_1, 32)
                    }
                    case 0x2a7c7c09 {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), not(3)), 32) { revert(0, 0) }
                        let value_2 := calldataload(4)
                        let size := 0
                        let _3 := 0
                        _3 := 0
                        size := 224
                        let memPtr := mload(64)
                        finalize_allocation(memPtr, 224)
                        let size_1 := 0
                        let _4 := 0
                        _4 := 0
                        size_1 := 224
                        calldatacopy(memPtr, calldatasize(), 224)
                        let memPtr_1 := mload(64)
                        finalize_allocation_44126(memPtr_1)
                        mstore(0, value_2)
                        mstore(32, 1)
                        mstore(memPtr_1, and(sload(/** @src 0:53695:53728  "marketState[id].settlementFeeCbp0" */ add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ keccak256(0, 64), /** @src 0:53695:53728  "marketState[id].settlementFeeCbp0" */ 2)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffff))
                        mstore(0, value_2)
                        mstore(32, 1)
                        mstore(/** @src 0:53681:54020  "[..." */ add(memPtr_1, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32), and(shr(16, sload(/** @src 0:53742:53775  "marketState[id].settlementFeeCbp1" */ add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ keccak256(0, 64), /** @src 0:53695:53728  "marketState[id].settlementFeeCbp0" */ 2))), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffff))
                        mstore(0, value_2)
                        mstore(32, 1)
                        mstore(/** @src 0:53681:54020  "[..." */ add(memPtr_1, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 64), and(shr(32, sload(/** @src 0:53789:53822  "marketState[id].settlementFeeCbp2" */ add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ keccak256(0, 64), /** @src 0:53695:53728  "marketState[id].settlementFeeCbp0" */ 2))), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffff))
                        mstore(0, value_2)
                        mstore(32, 1)
                        mstore(/** @src 0:53681:54020  "[..." */ add(memPtr_1, 96), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(shr(48, sload(/** @src 0:53836:53869  "marketState[id].settlementFeeCbp3" */ add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ keccak256(0, 64), /** @src 0:53695:53728  "marketState[id].settlementFeeCbp0" */ 2))), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffff))
                        mstore(0, value_2)
                        mstore(32, 1)
                        mstore(/** @src 0:53681:54020  "[..." */ add(memPtr_1, 128), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(shr(64, sload(/** @src 0:53883:53916  "marketState[id].settlementFeeCbp4" */ add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ keccak256(0, 64), /** @src 0:53695:53728  "marketState[id].settlementFeeCbp0" */ 2))), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffff))
                        mstore(0, value_2)
                        mstore(32, 1)
                        mstore(/** @src 0:53681:54020  "[..." */ add(memPtr_1, 160), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(shr(80, sload(/** @src 0:53930:53963  "marketState[id].settlementFeeCbp5" */ add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ keccak256(0, 64), /** @src 0:53695:53728  "marketState[id].settlementFeeCbp0" */ 2))), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffff))
                        mstore(0, value_2)
                        mstore(32, 1)
                        mstore(/** @src 0:53681:54020  "[..." */ add(memPtr_1, 192), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(shr(/** @src 0:53681:54020  "[..." */ 96, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ sload(/** @src 0:53977:54010  "marketState[id].settlementFeeCbp6" */ add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ keccak256(0, 64), /** @src 0:53695:53728  "marketState[id].settlementFeeCbp0" */ 2))), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffff))
                        let pos := mload(64)
                        let memPos_2 := pos
                        pos := pos
                        let srcPtr := memPtr_1
                        let i := 0
                        for { } lt(i, 7) { i := add(i, 1) }
                        {
                            mstore(pos, and(mload(srcPtr), 0xffff))
                            pos := add(pos, 32)
                            srcPtr := add(srcPtr, 32)
                        }
                        return(memPos_2, 224)
                    }
                    case 0x2abdc15e {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), not(3)), 96) { revert(0, 0) }
                        let value0_1 := abi_decode_address_44122()
                        let value_3 := calldataload(36)
                        let value2 := abi_decode_address_44128()
                        if iszero(/** @src 0:21318:21342  "msg.sender == feeClaimer" */ eq(/** @src 0:21318:21328  "msg.sender" */ caller(), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(sload(/** @src 0:21332:21342  "feeClaimer" */ 0x0b), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff)))
                        {
                            mstore(0, shl(230, 5467175))
                            revert(0, 4)
                        }
                        let _5 := and(value0_1, 0xffffffffffffffffffffffffffffffffffffffff)
                        mstore(0, _5)
                        mstore(32, /** @src 0:21371:21393  "claimableSettlementFee" */ 0x06)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let dataSlot_1 := keccak256(0, 64)
                        sstore(dataSlot_1, /** @src 0:21371:21410  "claimableSettlementFee[token] -= amount" */ checked_sub_uint256(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ sload(/** @src 0:21371:21410  "claimableSettlementFee[token] -= amount" */ dataSlot_1), value_3))
                        /// @src 0:21425:21490  "EventsLib.ClaimSettlementFee(msg.sender, token, amount, receiver)"
                        let _6 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                        mstore(_6, value_3)
                        /// @src 0:21425:21490  "EventsLib.ClaimSettlementFee(msg.sender, token, amount, receiver)"
                        log4(_6, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32, /** @src 0:21425:21490  "EventsLib.ClaimSettlementFee(msg.sender, token, amount, receiver)" */ 0x9e96510a66432371715fc0021aa4e375a1b788f31ed2732bff0f7b70acaeb8c2, /** @src 0:21318:21328  "msg.sender" */ caller(), /** @src 0:21425:21490  "EventsLib.ClaimSettlementFee(msg.sender, token, amount, receiver)" */ _5, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:21425:21490  "EventsLib.ClaimSettlementFee(msg.sender, token, amount, receiver)" */ value2, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                        /// @src 0:21546:21552  "amount"
                        fun_safeTransfer(value0_1, value2, value_3)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        return(0, 0)
                    }
                    case 0x2b507df8 {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                        let value_4 := and(sload(/** @src 0:14720:14747  "address public configurator" */ 9), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff)
                        let memPos_3 := mload(64)
                        mstore(memPos_3, value_4)
                        return(memPos_3, 32)
                    }
                    case 0x32292d96 {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), not(3)), 128) { revert(0, 0) }
                        let offset := calldataload(4)
                        if gt(offset, 0xffffffffffffffff) { revert(0, 0) }
                        let value0_2 := abi_decode_struct_Market(add(4, offset), calldatasize())
                        let value_5 := calldataload(36)
                        let value_6 := calldataload(68)
                        let _7 := and(abi_decode_address_44129(), 0xffffffffffffffffffffffffffffffffffffffff)
                        /// @src 0:32561:32621  "onBehalf == msg.sender || isAuthorized[onBehalf][msg.sender]"
                        let expr := /** @src 0:32561:32583  "onBehalf == msg.sender" */ eq(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _7, /** @src 0:32573:32583  "msg.sender" */ caller())
                        /// @src 0:32561:32621  "onBehalf == msg.sender || isAuthorized[onBehalf][msg.sender]"
                        if iszero(expr)
                        {
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            mstore(0, _7)
                            mstore(32, /** @src 0:32587:32599  "isAuthorized" */ 0x03)
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let dataSlot_2 := keccak256(0, 64)
                            /// @src 0:32587:32621  "isAuthorized[onBehalf][msg.sender]"
                            let dataSlot_3 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                            mstore(0, and(/** @src 0:32573:32583  "msg.sender" */ caller(), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                            mstore(0x20, /** @src 0:32587:32609  "isAuthorized[onBehalf]" */ dataSlot_2)
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            dataSlot_3 := keccak256(0, 0x40)
                            /// @src 0:32561:32621  "onBehalf == msg.sender || isAuthorized[onBehalf][msg.sender]"
                            expr := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(sload(/** @src 0:32587:32621  "isAuthorized[onBehalf][msg.sender]" */ dataSlot_3), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xff)
                        }
                        if iszero(expr)
                        {
                            mstore(0, shl(232, 8565801))
                            revert(0, 4)
                        }
                        /// @src 0:32661:32680  "touchMarket(market)"
                        let expr_1 := fun_touchMarket(value0_2)
                        /// @src 0:32716:32739  "market.collateralParams"
                        let _8 := add(value0_2, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 96)
                        let cleaned := and(mload(/** @src 0:32716:32756  "market.collateralParams[collateralIndex]" */ mload(memory_array_index_access_struct_CollateralParams_dyn(/** @src 0:32716:32739  "market.collateralParams" */ mload(_8), /** @src 0:32716:32756  "market.collateralParams[collateralIndex]" */ value_5))), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff)
                        mstore(0, expr_1)
                        mstore(32, 0)
                        let dataSlot_4 := keccak256(0, 64)
                        /// @src 0:32801:32823  "position[id][onBehalf]"
                        let dataSlot_5 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                        mstore(0, _7)
                        mstore(0x20, /** @src 0:32801:32813  "position[id]" */ dataSlot_4)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        dataSlot_5 := keccak256(0, 0x40)
                        /// @src 0:32857:32877  "_position.collateral"
                        let _9 := add(/** @src 0:32801:32823  "position[id][onBehalf]" */ dataSlot_5, /** @src 0:32857:32877  "_position.collateral" */ 3)
                        /// @src 0:32857:32894  "_position.collateral[collateralIndex]"
                        let _10, _11 := storage_array_index_access_uint128_(_9, value_5)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let value_7 := and(shr(shl(/** @src 0:32857:32877  "_position.collateral" */ 3, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _11), sload(/** @src 0:32857:32894  "_position.collateral[collateralIndex]" */ _10)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)
                        /// @src 0:32909:32941  "oldCollateral == 0 && assets > 0"
                        let expr_2 := /** @src 0:32909:32927  "oldCollateral == 0" */ iszero(value_7)
                        /// @src 0:32909:32941  "oldCollateral == 0 && assets > 0"
                        if expr_2
                        {
                            expr_2 := /** @src 0:32931:32941  "assets > 0" */ iszero(iszero(value_6))
                        }
                        /// @src 0:32905:33437  "if (oldCollateral == 0 && assets > 0) {..."
                        if expr_2
                        {
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let cleaned_1 := and(mload(/** @src 0:33059:33106  "market.collateralParams[collateralIndex].oracle" */ add(/** @src 0:33059:33099  "market.collateralParams[collateralIndex]" */ mload(memory_array_index_access_struct_CollateralParams_dyn(/** @src 0:33059:33082  "market.collateralParams" */ mload(_8), /** @src 0:33059:33099  "market.collateralParams[collateralIndex]" */ value_5)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 96)), 0xffffffffffffffffffffffffffffffffffffffff)
                            /// @src 0:33051:33115  "IOracle(market.collateralParams[collateralIndex].oracle).price()"
                            let _12 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                            /// @src 0:33051:33115  "IOracle(market.collateralParams[collateralIndex].oracle).price()"
                            mstore(_12, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(225, 0x501ad8ff))
                            /// @src 0:33051:33115  "IOracle(market.collateralParams[collateralIndex].oracle).price()"
                            let _13 := staticcall(gas(), cleaned_1, _12, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 4, /** @src 0:33051:33115  "IOracle(market.collateralParams[collateralIndex].oracle).price()" */ _12, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32)
                            /// @src 0:33051:33115  "IOracle(market.collateralParams[collateralIndex].oracle).price()"
                            if iszero(_13)
                            {
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                let pos_1 := mload(64)
                                returndatacopy(pos_1, 0, returndatasize())
                                revert(pos_1, returndatasize())
                            }
                            /// @src 0:33051:33115  "IOracle(market.collateralParams[collateralIndex].oracle).price()"
                            let expr_3 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                            /// @src 0:33051:33115  "IOracle(market.collateralParams[collateralIndex].oracle).price()"
                            if _13
                            {
                                let _14 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32
                                /// @src 0:33051:33115  "IOracle(market.collateralParams[collateralIndex].oracle).price()"
                                if gt(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32, /** @src 0:33051:33115  "IOracle(market.collateralParams[collateralIndex].oracle).price()" */ returndatasize()) { _14 := returndatasize() }
                                finalize_allocation(_12, _14)
                                let value0_3 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                                if slt(sub(/** @src 0:33051:33115  "IOracle(market.collateralParams[collateralIndex].oracle).price()" */ add(_12, _14), _12), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32) { revert(0, 0) }
                                value0_3 := mload(/** @src 0:33051:33115  "IOracle(market.collateralParams[collateralIndex].oracle).price()" */ _12)
                                expr_3 := value0_3
                            }
                            /// @src 0:33159:33185  "_position.collateralBitmap"
                            let _15 := add(/** @src 0:32801:32823  "position[id][onBehalf]" */ dataSlot_5, /** @src 0:33159:33185  "_position.collateralBitmap" */ 2)
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let _16 := shr(128, sload(/** @src 0:33159:33185  "_position.collateralBitmap" */ _15))
                            /// @src 12:1932:1951  "bitmap | (1 << bit)"
                            let _17 := or(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _16, /** @src 7:892:894  "16" */ shl(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ value_5, 1))
                            let cleaned_2 := and(_17, 0xffffffffffffffffffffffffffffffff)
                            /// @src 0:33223:33271  "_position.collateralBitmap = newCollateralBitmap"
                            update_storage_value_offset_uint128_to_uint128(_15, cleaned_2)
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let _18 := sub(/** @src 12:1208:1259  "x - ((x >> 1) & 0x55555555555555555555555555555555)" */ cleaned_2, /** @src 12:1213:1258  "(x >> 1) & 0x55555555555555555555555555555555" */ and(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shr(1, _17), /** @src 12:1224:1258  "0x55555555555555555555555555555555" */ 0x55555555555555555555555555555555))
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let _19 := add(/** @src 12:1278:1316  "x & 0x33333333333333333333333333333333" */ and(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _18, /** @src 12:1282:1316  "0x33333333333333333333333333333333" */ 0x33333333333333333333333333333333), /** @src 12:1321:1366  "(x >> 2) & 0x33333333333333333333333333333333" */ and(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shr(/** @src 0:33159:33185  "_position.collateralBitmap" */ 2, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _18), /** @src 12:1282:1316  "0x33333333333333333333333333333333" */ 0x33333333333333333333333333333333))
                            /// @src 7:892:894  "16"
                            if /** @src 0:33310:33381  "UtilsLib.countBits(newCollateralBitmap) <= MAX_COLLATERALS_PER_BORROWER" */ gt(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(shr(/** @src 12:1501:1504  "120" */ 0x78, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mul(/** @src 12:1385:1436  "(x + (x >> 4)) & 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f" */ and(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ add(and(_19, 0xffffffffffffffffffffffffffffffff), and(shr(4, _19), 0x0fffffffffffffffffffffffffffffff)), /** @src 12:1402:1436  "0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f" */ 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f), /** @src 12:1462:1496  "0x01010101010101010101010101010101" */ 0x01010101010101010101010101010101)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xff), /** @src 7:892:894  "16" */ 0x10)
                            {
                                mstore(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0, /** @src 7:892:894  "16" */ shl(224, 0x73290bb9))
                                revert(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0, 4)
                            }
                        }
                        /// @src 0:33487:33529  "UtilsLib.toUint128(oldCollateral + assets)"
                        let expr_4 := fun_toUint128(/** @src 0:33506:33528  "oldCollateral + assets" */ checked_add_uint256(value_7, value_6))
                        /// @src 0:33447:33484  "_position.collateral[collateralIndex]"
                        let _20, _21 := storage_array_index_access_uint128_(_9, value_5)
                        /// @src 0:33447:33529  "_position.collateral[collateralIndex] = UtilsLib.toUint128(oldCollateral + assets)"
                        update_storage_value_uint128_to_uint128(_20, _21, expr_4)
                        /// @src 0:33545:33622  "EventsLib.SupplyCollateral(msg.sender, id, collateralToken, assets, onBehalf)"
                        let _22 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                        /// @src 0:33545:33622  "EventsLib.SupplyCollateral(msg.sender, id, collateralToken, assets, onBehalf)"
                        log4(_22, sub(abi_encode_address_uint256(_22, /** @src 0:32573:32583  "msg.sender" */ caller(), /** @src 0:33545:33622  "EventsLib.SupplyCollateral(msg.sender, id, collateralToken, assets, onBehalf)" */ value_6), _22), 0x968f3d07613cff19e0b1a7b034a330cfc3c90e73c1112e14495b79f436a4a074, expr_1, cleaned, _7)
                        /// @src 0:33710:33716  "assets"
                        fun_safeTransferFrom(cleaned, /** @src 0:32573:32583  "msg.sender" */ caller(), /** @src 0:33703:33707  "this" */ address(), /** @src 0:33710:33716  "assets" */ value_6)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        return(0, 0)
                    }
                    case 0x462e59b4 {
                        if callvalue() { revert(0, 0) }
                        let param, param_1 := abi_decode_bytes32t_uint256(calldatasize())
                        mstore(0, param)
                        mstore(0x20, /** @src 0:20222:20233  "marketState" */ 0x01)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let dataSlot_6 := keccak256(0, 64)
                        if iszero(/** @src 0:20255:20278  "msg.sender == feeSetter" */ eq(/** @src 0:20255:20265  "msg.sender" */ caller(), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(sload(/** @src 0:20269:20278  "feeSetter" */ 0x0a), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff)))
                        {
                            mstore(0, shl(224, 0x7155bb19))
                            revert(0, 4)
                        }
                        /// @src 0:20334:20352  "MAX_CONTINUOUS_FEE"
                        let ret_2 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                        /// @src 7:711:755  "uint32(uint256(0.01e18) / uint256(365 days))"
                        ret_2 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x12e687bf
                        /// @src 7:711:755  "uint32(uint256(0.01e18) / uint256(365 days))"
                        if /** @src 0:20314:20352  "newContinuousFee <= MAX_CONTINUOUS_FEE" */ gt(param_1, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ ret_2)
                        /// @src 7:711:755  "uint32(uint256(0.01e18) / uint256(365 days))"
                        {
                            mstore(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0, /** @src 7:711:755  "uint32(uint256(0.01e18) / uint256(365 days))" */ shl(224, 0x39ee5d9b))
                            revert(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0, 4)
                        }
                        /// @src 0:20396:20420  "_marketState.tickSpacing"
                        let _23 := add(dataSlot_6, 2)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        if /** @src 0:20396:20424  "_marketState.tickSpacing > 0" */ iszero(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(shr(144, sload(/** @src 0:20396:20420  "_marketState.tickSpacing" */ _23)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xff))
                        {
                            mstore(0, shl(224, 0x96e13529))
                            revert(0, 4)
                        }
                        /// @src 0:20574:20627  "_marketState.continuousFee = uint32(newContinuousFee)"
                        update_storage_value_offset_uint32_to_uint32(_23, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:20603:20627  "uint32(newContinuousFee)" */ param_1, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffff))
                        /// @src 0:20642:20696  "EventsLib.SetMarketContinuousFee(id, newContinuousFee)"
                        let _24 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                        mstore(_24, param_1)
                        /// @src 0:20642:20696  "EventsLib.SetMarketContinuousFee(id, newContinuousFee)"
                        log2(_24, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x20, /** @src 0:20642:20696  "EventsLib.SetMarketContinuousFee(id, newContinuousFee)" */ 0xbf609558d120b32620da3fe5220a2e268bda00456bf69e25e6a2c517114cce9b, param)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        return(0, 0)
                    }
                    case 0x4d98a93b {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), not(3)), 32) { revert(0, 0) }
                        let value_8 := calldataload(4)
                        if iszero(/** @src 0:16510:16536  "msg.sender == configurator" */ eq(/** @src 0:16510:16520  "msg.sender" */ caller(), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(sload(/** @src 0:16524:16536  "configurator" */ 0x09), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff)))
                        {
                            mstore(0, shl(228, 0x033b71e1))
                            revert(0, 4)
                        }
                        /// @src 7:190:194  "1e18"
                        if /** @src 0:16575:16586  "lltv <= WAD" */ gt(value_8, /** @src 7:190:194  "1e18" */ 0x0de0b6b3a7640000)
                        {
                            mstore(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0, /** @src 7:190:194  "1e18" */ shl(224, 0x021aa0d7))
                            revert(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0, 4)
                        }
                        mstore(0, value_8)
                        mstore(32, /** @src 0:16612:16625  "isLltvEnabled" */ 0x07)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let dataSlot_7 := keccak256(0, 64)
                        /// @src 7:190:194  "1e18"
                        sstore(dataSlot_7, or(and(sload(dataSlot_7), not(255)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 1))
                        /// @src 0:16653:16679  "EventsLib.EnableLltv(lltv)"
                        let _25 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                        mstore(_25, value_8)
                        /// @src 0:16653:16679  "EventsLib.EnableLltv(lltv)"
                        log1(_25, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32, /** @src 0:16653:16679  "EventsLib.EnableLltv(lltv)" */ 0x297b80e7a896fad470c630f6575072d609bde997260ff3db851939405ec29139)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        return(0, 0)
                    }
                    case 0x4f80fe10 {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), not(3)), 128) { revert(0, 0) }
                        let offset_1 := calldataload(4)
                        if gt(offset_1, 0xffffffffffffffff) { revert(0, 0) }
                        let value0_4, value1 := abi_decode_array_address_dyn_calldata(add(4, offset_1), calldatasize())
                        let offset_2 := calldataload(36)
                        if gt(offset_2, 0xffffffffffffffff) { revert(0, 0) }
                        let value2_1, value3 := abi_decode_array_address_dyn_calldata(add(4, offset_2), calldatasize())
                        let value4 := abi_decode_address_44128()
                        let offset_3 := calldataload(100)
                        if gt(offset_3, 0xffffffffffffffff) { revert(0, 0) }
                        let value5, value6 := abi_decode_bytes_calldata(add(4, offset_3), calldatasize())
                        if iszero(/** @src 0:42530:42560  "tokens.length == assets.length" */ eq(value1, value3))
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        {
                            mstore(0, shl(224, 0xf0732dd7))
                            revert(0, 4)
                        }
                        let _26 := and(/** @src 0:42597:42654  "EventsLib.FlashLoan(msg.sender, tokens, assets, callback)" */ value4, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff)
                        /// @src 0:42597:42654  "EventsLib.FlashLoan(msg.sender, tokens, assets, callback)"
                        let _27 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                        mstore(_27, 64)
                        let tail := abi_encode_array_address_dyn_calldata(value0_4, value1, add(_27, 64))
                        mstore(add(_27, 32), sub(tail, _27))
                        /// @src 0:42597:42654  "EventsLib.FlashLoan(msg.sender, tokens, assets, callback)"
                        log3(_27, sub(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ abi_encode_array_uint256_dyn_calldata(value2_1, value3, tail), /** @src 0:42597:42654  "EventsLib.FlashLoan(msg.sender, tokens, assets, callback)" */ _27), 0x3a1534fae3196d51e11f8e6ba02e8a834d8eded5eb826d766d3fd048f3c6b83c, /** @src 0:42617:42627  "msg.sender" */ caller(), /** @src 0:42597:42654  "EventsLib.FlashLoan(msg.sender, tokens, assets, callback)" */ _26)
                        /// @src 0:42669:42682  "uint256 i = 0"
                        let var_i := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                        /// @src 0:42664:42793  "for (uint256 i = 0; i < tokens.length; i++) {..."
                        for { }
                        /** @src 0:42684:42701  "i < tokens.length" */ lt(var_i, value1)
                        /// @src 0:42669:42682  "uint256 i = 0"
                        {
                            /// @src 0:42703:42706  "i++"
                            var_i := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ add(/** @src 0:42703:42706  "i++" */ var_i, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 1)
                        }
                        /// @src 0:42703:42706  "i++"
                        {
                            /// @src 0:42751:42760  "tokens[i]"
                            let expr_5 := read_from_calldatat_address(calldata_array_index_access_address_dyn_calldata(value0_4, value1, var_i))
                            /// @src 0:42772:42781  "assets[i]"
                            fun_safeTransfer(expr_5, value4, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(/** @src 0:42772:42781  "assets[i]" */ calldata_array_index_access_address_dyn_calldata(value2_1, value3, var_i)))
                        }
                        /// @src 0:42823:42897  "IFlashLoanCallback(callback).onFlashLoan(msg.sender, tokens, assets, data)"
                        let _28 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                        /// @src 0:42823:42897  "IFlashLoanCallback(callback).onFlashLoan(msg.sender, tokens, assets, data)"
                        mstore(_28, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(224, 0xd1f260c3))
                        mstore(/** @src 0:42823:42897  "IFlashLoanCallback(callback).onFlashLoan(msg.sender, tokens, assets, data)" */ add(_28, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 4), /** @src 0:42617:42627  "msg.sender" */ caller())
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(add(/** @src 0:42823:42897  "IFlashLoanCallback(callback).onFlashLoan(msg.sender, tokens, assets, data)" */ _28, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 36), 128)
                        let tail_1 := abi_encode_array_address_dyn_calldata(value0_4, value1, add(/** @src 0:42823:42897  "IFlashLoanCallback(callback).onFlashLoan(msg.sender, tokens, assets, data)" */ _28, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 132))
                        mstore(add(/** @src 0:42823:42897  "IFlashLoanCallback(callback).onFlashLoan(msg.sender, tokens, assets, data)" */ _28, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 68), add(sub(tail_1, /** @src 0:42823:42897  "IFlashLoanCallback(callback).onFlashLoan(msg.sender, tokens, assets, data)" */ _28), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(3)))
                        let tail_2 := abi_encode_array_uint256_dyn_calldata(value2_1, value3, tail_1)
                        mstore(add(/** @src 0:42823:42897  "IFlashLoanCallback(callback).onFlashLoan(msg.sender, tokens, assets, data)" */ _28, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 100), add(sub(tail_2, /** @src 0:42823:42897  "IFlashLoanCallback(callback).onFlashLoan(msg.sender, tokens, assets, data)" */ _28), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(3)))
                        /// @src 0:42823:42897  "IFlashLoanCallback(callback).onFlashLoan(msg.sender, tokens, assets, data)"
                        let _29 := call(gas(), _26, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0, /** @src 0:42823:42897  "IFlashLoanCallback(callback).onFlashLoan(msg.sender, tokens, assets, data)" */ _28, sub(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ abi_encode_bytes_calldata(value5, value6, tail_2), /** @src 0:42823:42897  "IFlashLoanCallback(callback).onFlashLoan(msg.sender, tokens, assets, data)" */ _28), _28, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32)
                        /// @src 0:42823:42897  "IFlashLoanCallback(callback).onFlashLoan(msg.sender, tokens, assets, data)"
                        if iszero(_29)
                        {
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let pos_2 := mload(64)
                            returndatacopy(pos_2, 0, returndatasize())
                            revert(pos_2, returndatasize())
                        }
                        /// @src 0:42823:42897  "IFlashLoanCallback(callback).onFlashLoan(msg.sender, tokens, assets, data)"
                        let expr_6 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                        /// @src 0:42823:42897  "IFlashLoanCallback(callback).onFlashLoan(msg.sender, tokens, assets, data)"
                        if _29
                        {
                            let _30 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32
                            /// @src 0:42823:42897  "IFlashLoanCallback(callback).onFlashLoan(msg.sender, tokens, assets, data)"
                            if gt(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32, /** @src 0:42823:42897  "IFlashLoanCallback(callback).onFlashLoan(msg.sender, tokens, assets, data)" */ returndatasize()) { _30 := returndatasize() }
                            finalize_allocation(_28, _30)
                            let value0_5 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                            if slt(sub(/** @src 0:42823:42897  "IFlashLoanCallback(callback).onFlashLoan(msg.sender, tokens, assets, data)" */ add(_28, _30), _28), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32) { revert(0, 0) }
                            value0_5 := mload(/** @src 0:42823:42897  "IFlashLoanCallback(callback).onFlashLoan(msg.sender, tokens, assets, data)" */ _28)
                            expr_6 := value0_5
                        }
                        /// @src 7:1030:1074  "keccak256(\"morpho.midnight.callbackSuccess\")"
                        if iszero(/** @src 0:42823:42917  "IFlashLoanCallback(callback).onFlashLoan(msg.sender, tokens, assets, data) == CALLBACK_SUCCESS" */ eq(expr_6, /** @src 7:1030:1074  "keccak256(\"morpho.midnight.callbackSuccess\")" */ 0x7f87788ea698181ea4d28d1576d0ba4fc92c0dbe5bf75b43692af2ce91dbaea2))
                        {
                            mstore(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0, /** @src 7:1030:1074  "keccak256(\"morpho.midnight.callbackSuccess\")" */ shl(228, 0x0a429c87))
                            revert(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0, 4)
                        }
                        /// @src 0:42991:43004  "uint256 i = 0"
                        let var_i_1 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                        /// @src 0:42986:43134  "for (uint256 i = 0; i < tokens.length; i++) {..."
                        for { }
                        /** @src 0:43006:43023  "i < tokens.length" */ lt(var_i_1, value1)
                        /// @src 0:42991:43004  "uint256 i = 0"
                        {
                            /// @src 0:43025:43028  "i++"
                            var_i_1 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ add(/** @src 0:43025:43028  "i++" */ var_i_1, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 1)
                        }
                        /// @src 0:43025:43028  "i++"
                        {
                            /// @src 0:43077:43086  "tokens[i]"
                            let expr_7 := read_from_calldatat_address(calldata_array_index_access_address_dyn_calldata(value0_4, value1, var_i_1))
                            /// @src 0:43113:43122  "assets[i]"
                            fun_safeTransferFrom(expr_7, value4, /** @src 0:43106:43110  "this" */ address(), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(/** @src 0:43113:43122  "assets[i]" */ calldata_array_index_access_address_dyn_calldata(value2_1, value3, var_i_1)))
                        }
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        return(0, 0)
                    }
                    case 0x5308a18f {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), not(3)), 32) { revert(0, 0) }
                        mstore(0, and(abi_decode_address_44122(), 0xffffffffffffffffffffffffffffffffffffffff))
                        mstore(32, /** @src 0:14513:14576  "mapping(address token => uint256) public claimableSettlementFee" */ 6)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let _31 := sload(keccak256(0, 64))
                        let memPos_4 := mload(64)
                        mstore(memPos_4, _31)
                        return(memPos_4, 32)
                    }
                    case 0x53a6332b {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), not(3)), 32) { revert(0, 0) }
                        mstore(0, calldataload(4))
                        mstore(32, 1)
                        let cleaned_3 := and(sload(keccak256(0, 64)), 0xffffffffffffffffffffffffffffffff)
                        let memPos_5 := mload(64)
                        mstore(memPos_5, cleaned_3)
                        return(memPos_5, 32)
                    }
                    case 0x545e513a {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), not(3)), 64) { revert(0, 0) }
                        let offset_4 := calldataload(4)
                        if gt(offset_4, 0xffffffffffffffff) { revert(0, 0) }
                        let value0_6 := abi_decode_struct_Market(add(4, offset_4), calldatasize())
                        /// @src 0:47561:47594  "_updatePosition(market, id, user)"
                        let expr_component, expr_component_1, expr_component_2 := fun_updatePosition(value0_6, /** @src 0:47525:47544  "touchMarket(market)" */ fun_touchMarket(value0_6), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ abi_decode_address_44120())
                        let memPos_6 := mload(64)
                        return(memPos_6, sub(abi_encode_uint128_uint128_uint128(memPos_6, expr_component, expr_component_1, expr_component_2), memPos_6))
                    }
                    case 0x570b935f {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), not(3)), 32) { revert(0, 0) }
                        mstore(0, calldataload(4))
                        mstore(32, 1)
                        let _32 := shr(128, sload(keccak256(0, 64)))
                        let memPos_7 := mload(64)
                        mstore(memPos_7, _32)
                        return(memPos_7, 32)
                    }
                    case 0x575272a8 {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), not(3)), 96) { revert(0, 0) }
                        let offset_5 := calldataload(4)
                        if gt(offset_5, 0xffffffffffffffff) { revert(0, 0) }
                        let value0_7 := abi_decode_struct_Market(add(4, offset_5), calldatasize())
                        let value_9 := calldataload(36)
                        let value2_2 := abi_decode_address_44128()
                        /// @src 0:21682:21701  "touchMarket(market)"
                        let expr_8 := fun_touchMarket(value0_7)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(0, expr_8)
                        mstore(32, 1)
                        let dataSlot_8 := keccak256(0, 64)
                        if iszero(/** @src 0:21779:21803  "msg.sender == feeClaimer" */ eq(/** @src 0:21779:21789  "msg.sender" */ caller(), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(sload(/** @src 0:21793:21803  "feeClaimer" */ 0x0b), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff)))
                        {
                            mstore(0, shl(230, 5467175))
                            revert(0, 4)
                        }
                        /// @src 0:21869:21895  "UtilsLib.toUint128(amount)"
                        let expr_9 := fun_toUint128(value_9)
                        /// @src 0:21833:21865  "_marketState.continuousFeeCredit"
                        let _33 := add(dataSlot_8, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 1)
                        /// @src 0:21833:21895  "_marketState.continuousFeeCredit -= UtilsLib.toUint128(amount)"
                        update_storage_value_offset_uint128_to_uint128(_33, checked_sub_uint128(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shr(128, sload(/** @src 0:21833:21895  "_marketState.continuousFeeCredit -= UtilsLib.toUint128(amount)" */ _33)), expr_9))
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        sstore(/** @src 0:21905:21958  "_marketState.totalUnits -= UtilsLib.toUint128(amount)" */ dataSlot_8, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ or(and(sload(/** @src 0:21905:21958  "_marketState.totalUnits -= UtilsLib.toUint128(amount)" */ dataSlot_8), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(0xffffffffffffffffffffffffffffffff)), and(/** @src 0:21905:21958  "_marketState.totalUnits -= UtilsLib.toUint128(amount)" */ checked_sub_uint128(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(sload(/** @src 0:21905:21958  "_marketState.totalUnits -= UtilsLib.toUint128(amount)" */ dataSlot_8), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff), /** @src 0:21932:21958  "UtilsLib.toUint128(amount)" */ fun_toUint128(value_9)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)))
                        sstore(/** @src 0:21968:22023  "_marketState.withdrawable -= UtilsLib.toUint128(amount)" */ _33, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ or(and(sload(/** @src 0:21968:22023  "_marketState.withdrawable -= UtilsLib.toUint128(amount)" */ _33), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(0xffffffffffffffffffffffffffffffff)), and(/** @src 0:21968:22023  "_marketState.withdrawable -= UtilsLib.toUint128(amount)" */ checked_sub_uint128(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(sload(/** @src 0:21968:22023  "_marketState.withdrawable -= UtilsLib.toUint128(amount)" */ _33), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff), /** @src 0:21997:22023  "UtilsLib.toUint128(amount)" */ fun_toUint128(value_9)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)))
                        /// @src 0:22039:22101  "EventsLib.ClaimContinuousFee(msg.sender, id, amount, receiver)"
                        let _34 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                        mstore(_34, value_9)
                        /// @src 0:22039:22101  "EventsLib.ClaimContinuousFee(msg.sender, id, amount, receiver)"
                        log4(_34, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32, /** @src 0:22039:22101  "EventsLib.ClaimContinuousFee(msg.sender, id, amount, receiver)" */ 0xd64453ff5184816a23d670b5224717cd441c4a7cd5f4e7dbc30f8511d35f597b, /** @src 0:21779:21789  "msg.sender" */ caller(), /** @src 0:22039:22101  "EventsLib.ClaimContinuousFee(msg.sender, id, amount, receiver)" */ expr_8, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:22039:22101  "EventsLib.ClaimContinuousFee(msg.sender, id, amount, receiver)" */ value2_2, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                        /// @src 0:22169:22175  "amount"
                        fun_safeTransfer(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(mload(/** @src 0:22141:22157  "market.loanToken" */ add(value0_7, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 64)), 0xffffffffffffffffffffffffffffffffffffffff), /** @src 0:22169:22175  "amount" */ value2_2, value_9)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        return(0, 0)
                    }
                    case 0x5ce648dc {
                        if callvalue() { revert(0, 0) }
                        let param_2, param_3, param_4 := abi_decode_struct_Markett_bytes32t_address(calldatasize())
                        let ret_3 := fun_isHealthy(param_2, param_3, param_4)
                        let memPos_8 := mload(64)
                        mstore(memPos_8, iszero(iszero(ret_3)))
                        return(memPos_8, 32)
                    }
                    case 0x5f59ebd8 {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), not(3)), 96) { revert(0, 0) }
                        let value0_8 := abi_decode_address_44122()
                        let value_10 := calldataload(36)
                        let value_11 := calldataload(68)
                        if iszero(/** @src 0:19551:19574  "msg.sender == feeSetter" */ eq(/** @src 0:19551:19561  "msg.sender" */ caller(), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(sload(/** @src 0:19565:19574  "feeSetter" */ 0x0a), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff)))
                        {
                            mstore(0, shl(224, 0x7155bb19))
                            revert(0, 4)
                        }
                        if /** @src 0:19610:19620  "index <= 6" */ gt(value_10, /** @src 0:19619:19620  "6" */ 0x06)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        {
                            mstore(0, shl(224, 0x37f6201f))
                            revert(0, 4)
                        }
                        if /** @src 0:19658:19701  "newSettlementFee <= maxSettlementFee(index)" */ gt(value_11, /** @src 0:19678:19701  "maxSettlementFee(index)" */ fun_maxSettlementFee(value_10))
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        {
                            mstore(0, shl(226, 0x3faa18af))
                            revert(0, 4)
                        }
                        /// @src 7:263:267  "1e12"
                        if iszero(/** @src 0:19745:19772  "newSettlementFee % CBP == 0" */ iszero(/** @src 7:263:267  "1e12" */ mod(value_11, 0xe8d4a51000)))
                        {
                            mstore(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0, /** @src 7:263:267  "1e12" */ shl(224, 0x1468c5cb))
                            revert(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0, 4)
                        }
                        let _35 := and(value0_8, 0xffffffffffffffffffffffffffffffffffffffff)
                        mstore(0, _35)
                        mstore(32, 4)
                        /// @src 0:19927:19968  "defaultSettlementFeeCbp[loanToken][index]"
                        let _36, _37 := storage_array_index_access_uint(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ keccak256(0, 64), /** @src 0:19927:19968  "defaultSettlementFeeCbp[loanToken][index]" */ value_10)
                        /// @src 7:263:267  "1e12"
                        let _38 := sload(_36)
                        let shiftBits := shl(3, _37)
                        sstore(_36, or(and(_38, not(/** @src 7:892:894  "16" */ shl(/** @src 7:263:267  "1e12" */ shiftBits, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffff))), /** @src 7:263:267  "1e12" */ shl(shiftBits, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(div(value_11, /** @src 7:263:267  "1e12" */ 0xe8d4a51000), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffff))))
                        /// @src 0:20016:20085  "EventsLib.SetDefaultSettlementFee(loanToken, index, newSettlementFee)"
                        let _39 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                        mstore(_39, value_11)
                        /// @src 0:20016:20085  "EventsLib.SetDefaultSettlementFee(loanToken, index, newSettlementFee)"
                        log3(_39, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32, /** @src 0:20016:20085  "EventsLib.SetDefaultSettlementFee(loanToken, index, newSettlementFee)" */ 0x4a3a913aa0adf6796a2827443c326f4c5e2c345f39314b893d3233751793b824, _35, value_10)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        return(0, 0)
                    }
                    case 0x65e4ad9e {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), not(3)), 64) { revert(0, 0) }
                        let value0_9 := abi_decode_address_44122()
                        let value1_1 := abi_decode_address_44120()
                        mstore(0, and(value0_9, 0xffffffffffffffffffffffffffffffffffffffff))
                        mstore(32, /** @src 0:14275:14361  "mapping(address authorizer => mapping(address authorized => bool)) public isAuthorized" */ 3)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let dataSlot_9 := keccak256(0, 64)
                        /// @src 0:14275:14361  "mapping(address authorizer => mapping(address authorized => bool)) public isAuthorized"
                        let dataSlot_10 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                        mstore(0, and(/** @src 0:14275:14361  "mapping(address authorizer => mapping(address authorized => bool)) public isAuthorized" */ value1_1, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                        mstore(0x20, /** @src 0:14275:14361  "mapping(address authorizer => mapping(address authorized => bool)) public isAuthorized" */ dataSlot_9)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        dataSlot_10 := keccak256(0, 0x40)
                        let value_12 := and(sload(/** @src 0:14275:14361  "mapping(address authorizer => mapping(address authorized => bool)) public isAuthorized" */ dataSlot_10), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xff)
                        let memPos_9 := mload(64)
                        mstore(memPos_9, iszero(iszero(value_12)))
                        return(memPos_9, 32)
                    }
                    case 0x6a14c9ef {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), not(3)), 224) { revert(0, 0) }
                        let offset_6 := calldataload(4)
                        if gt(offset_6, 0xffffffffffffffff) { revert(0, 0) }
                        if slt(add(sub(calldatasize(), offset_6), not(3)), 0x01e0) { revert(0, 0) }
                        mstore(0x0180, mload(64))
                        let newFreePtr := add(mload(0x0180), 0x01e0)
                        if or(gt(newFreePtr, 0xffffffffffffffff), lt(newFreePtr, mload(0x0180)))
                        {
                            mstore(0, shl(224, 0x4e487b71))
                            mstore(4, 0x41)
                            revert(0, 0x24)
                        }
                        mstore(64, newFreePtr)
                        let offset_7 := calldataload(add(4, offset_6))
                        if gt(offset_7, 0xffffffffffffffff) { revert(0, 0) }
                        mstore(mload(0x0180), abi_decode_struct_Market(add(add(offset_6, offset_7), 4), calldatasize()))
                        let _40 := abi_decode_bool(add(offset_6, 36))
                        mstore(add(mload(0x0180), 32), _40)
                        let _41 := abi_decode_address(add(offset_6, 68))
                        mstore(add(mload(0x0180), 64), _41)
                        mstore(add(mload(0x0180), 96), calldataload(add(offset_6, 100)))
                        mstore(add(mload(0x0180), 128), calldataload(add(offset_6, 132)))
                        mstore(add(mload(0x0180), 160), calldataload(add(offset_6, 164)))
                        mstore(add(mload(0x0180), 192), calldataload(add(offset_6, 196)))
                        let _42 := abi_decode_address(add(offset_6, 228))
                        mstore(add(mload(0x0180), 224), _42)
                        let offset_8 := calldataload(add(offset_6, 260))
                        if gt(offset_8, 0xffffffffffffffff) { revert(0, 0) }
                        let _43 := abi_decode_bytes(add(add(offset_6, offset_8), 4), calldatasize())
                        mstore(add(mload(0x0180), 256), _43)
                        let _44 := abi_decode_address(add(offset_6, 292))
                        mstore(add(mload(0x0180), 288), _44)
                        let _45 := abi_decode_address(add(offset_6, 324))
                        mstore(add(mload(0x0180), 320), _45)
                        let _46 := abi_decode_bool(add(offset_6, 356))
                        mstore(add(mload(0x0180), 352), _46)
                        let _47 := abi_decode_uint128(add(offset_6, 388))
                        mstore(add(mload(0x0180), 384), _47)
                        let _48 := abi_decode_uint128(add(offset_6, 420))
                        mstore(add(mload(0x0180), 416), _48)
                        mstore(add(mload(0x0180), 448), calldataload(add(offset_6, 452)))
                        let offset_9 := calldataload(36)
                        if gt(offset_9, 0xffffffffffffffff) { revert(0, 0) }
                        let value1_2 := abi_decode_bytes(add(4, offset_9), calldatasize())
                        mstore(0x0220, abi_decode_address_44129())
                        mstore(0x0120, abi_decode_address_44141())
                        mstore(0xc0, 0)
                        mstore(0xc0, calldataload(164))
                        if iszero(eq(mload(0xc0), and(mload(0xc0), 0xffffffffffffffffffffffffffffffffffffffff))) { revert(0, 0) }
                        if gt(calldataload(196), 0xffffffffffffffff) { revert(0, 0) }
                        mstore(0x0140, abi_decode_bytes(add(4, calldataload(196)), calldatasize()))
                        /// @src 0:23215:23269  "taker == msg.sender || isAuthorized[taker][msg.sender]"
                        let expr_10 := /** @src 0:23215:23234  "taker == msg.sender" */ eq(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:23215:23234  "taker == msg.sender" */ mload(0x0220), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff), /** @src 0:23224:23234  "msg.sender" */ caller())
                        /// @src 0:23215:23269  "taker == msg.sender || isAuthorized[taker][msg.sender]"
                        if iszero(expr_10)
                        {
                            /// @src 0:23238:23257  "isAuthorized[taker]"
                            let _49 := mapping_index_access_mapping_address_uint32_of_address(mload(0x0220))
                            /// @src 0:23238:23269  "isAuthorized[taker][msg.sender]"
                            let dataSlot_11 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                            mstore(0, and(/** @src 0:23224:23234  "msg.sender" */ caller(), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                            mstore(0x20, /** @src 0:23238:23257  "isAuthorized[taker]" */ _49)
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            dataSlot_11 := keccak256(0, 0x40)
                            /// @src 0:23238:23269  "isAuthorized[taker][msg.sender]"
                            let value_13 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                            value_13 := and(sload(/** @src 0:23238:23269  "isAuthorized[taker][msg.sender]" */ dataSlot_11), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xff)
                            /// @src 0:23215:23269  "taker == msg.sender || isAuthorized[taker][msg.sender]"
                            expr_10 := value_13
                        }
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        if iszero(expr_10)
                        {
                            mstore(0, shl(224, 0x336c6d7f))
                            revert(0, 4)
                        }
                        /// @src 0:23314:23339  "touchMarket(offer.market)"
                        mstore(0x0200, fun_touchMarket(/** @src 0:23326:23338  "offer.market" */ mload(mload(0x0180))))
                        /// @src 0:23384:23399  "marketState[id]"
                        let dataSlot_12 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                        mstore(0, mload(0x0200))
                        mstore(32, /** @src 0:23384:23395  "marketState" */ 0x01)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        dataSlot_12 := keccak256(0, 64)
                        let _50 := sload(/** @src 0:23417:23440  "_marketState.lossFactor" */ dataSlot_12)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let value_14 := 0
                        value_14 := shr(128, _50)
                        if iszero(/** @src 0:23417:23460  "_marketState.lossFactor < type(uint128).max" */ lt(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ value_14, 0xffffffffffffffffffffffffffffffff))
                        {
                            mstore(0, shl(226, 0x200ec5d9))
                            revert(0, 4)
                        }
                        let _51 := mload(add(mload(0x0180), 416))
                        let cleaned_4 := 0
                        cleaned_4 := and(_51, 0xffffffffffffffffffffffffffffffff)
                        let _52 := mload(add(mload(0x0180), 384))
                        let cleaned_5 := 0
                        cleaned_5 := and(_52, 0xffffffffffffffffffffffffffffffff)
                        /// @src 0:23534:23553  "offer.maxUnits == 0"
                        let cleaned_6 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                        cleaned_6 := cleaned_5
                        /// @src 0:23534:23553  "offer.maxUnits == 0"
                        let _53 := iszero(cleaned_5)
                        /// @src 0:23507:23554  "(offer.maxAssets == 0) != (offer.maxUnits == 0)"
                        let cleaned_7 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                        cleaned_7 := _53
                        if /** @src 0:23507:23554  "(offer.maxAssets == 0) != (offer.maxUnits == 0)" */ eq(/** @src 0:23508:23528  "offer.maxAssets == 0" */ iszero(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ cleaned_4), /** @src 0:23507:23554  "(offer.maxAssets == 0) != (offer.maxUnits == 0)" */ _53)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        {
                            mstore(0, shl(225, 0x652da017))
                            revert(0, 4)
                        }
                        let _54 := sload(/** @src 0:23593:23619  "_marketState.continuousFee" */ add(dataSlot_12, 2))
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let value_15 := 0
                        value_15 := and(shr(112, _54), 0xffffffff)
                        if /** @src 0:23593:23645  "_marketState.continuousFee <= offer.continuousFeeCap" */ gt(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ value_15, /** @src 7:234:238  "1e36" */ mload(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ add(mload(0x0180), 448)))
                        {
                            mstore(0, shl(224, 0xd8c09575))
                            revert(0, 4)
                        }
                        /// @src 7:234:238  "1e36"
                        let _55 := mload(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ add(mload(0x0180), 160))
                        let value_16 := 0
                        value_16 := and(shr(144, _54), 0xff)
                        /// @src 0:23694:23731  "offer.tick % _marketState.tickSpacing"
                        let value_17 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                        value_17 := value_16
                        if iszero(/** @src 0:23694:23736  "offer.tick % _marketState.tickSpacing == 0" */ iszero(/** @src 0:23694:23731  "offer.tick % _marketState.tickSpacing" */ mod_uint256(_55, value_16)))
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        {
                            mstore(0, shl(228, 0x06e17dfb))
                            revert(0, 4)
                        }
                        if /** @src 0:23776:23806  "block.timestamp >= offer.start" */ lt(/** @src 0:23776:23791  "block.timestamp" */ timestamp(), /** @src 7:234:238  "1e36" */ mload(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ add(mload(0x0180), 96)))
                        {
                            mstore(0, shl(225, 0x1ef86fbb))
                            revert(0, 4)
                        }
                        if /** @src 0:23844:23875  "block.timestamp <= offer.expiry" */ gt(/** @src 0:23776:23791  "block.timestamp" */ timestamp(), /** @src 7:234:238  "1e36" */ mload(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ add(mload(0x0180), 128)))
                        {
                            mstore(0, shl(224, 0x9cb13087))
                            revert(0, 4)
                        }
                        let _56 := mload(add(mload(0x0180), 64))
                        let cleaned_8 := 0
                        cleaned_8 := and(_56, 0xffffffffffffffffffffffffffffffffffffffff)
                        /// @src 0:23910:23930  "offer.maker != taker"
                        let cleaned_9 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                        cleaned_9 := cleaned_8
                        if /** @src 0:23910:23930  "offer.maker != taker" */ eq(cleaned_8, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:23215:23234  "taker == msg.sender" */ mload(0x0220), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                        {
                            mstore(0, shl(225, 0x08b73f79))
                            revert(0, 4)
                        }
                        let _57 := mload(add(mload(0x0180), 32))
                        let cleaned_10 := 0
                        cleaned_10 := iszero(iszero(_57))
                        /// @src 0:23974:24069  "offer.buy ? offer.receiverIfMakerIsSeller == address(0) : receiverIfTakerIsSeller == address(0)"
                        let expr_11 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                        /// @src 0:23974:24069  "offer.buy ? offer.receiverIfMakerIsSeller == address(0) : receiverIfTakerIsSeller == address(0)"
                        switch cleaned_10
                        case 0 {
                            expr_11 := /** @src 0:24032:24069  "receiverIfTakerIsSeller == address(0)" */ iszero(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:24032:24069  "receiverIfTakerIsSeller == address(0)" */ mload(0x0120), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                        }
                        default /// @src 0:23974:24069  "offer.buy ? offer.receiverIfMakerIsSeller == address(0) : receiverIfTakerIsSeller == address(0)"
                        {
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let _58 := mload(add(mload(0x0180), 288))
                            let cleaned_11 := 0
                            cleaned_11 := and(_58, 0xffffffffffffffffffffffffffffffffffffffff)
                            /// @src 0:23974:24069  "offer.buy ? offer.receiverIfMakerIsSeller == address(0) : receiverIfTakerIsSeller == address(0)"
                            expr_11 := /** @src 0:23986:24029  "offer.receiverIfMakerIsSeller == address(0)" */ iszero(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ cleaned_11)
                        }
                        if iszero(expr_11)
                        {
                            mstore(0, shl(224, 0x58852d43))
                            revert(0, 4)
                        }
                        let _59 := mload(add(mload(0x0180), 64))
                        let cleaned_12 := 0
                        cleaned_12 := and(_59, 0xffffffffffffffffffffffffffffffffffffffff)
                        /// @src 0:24137:24162  "isAuthorized[offer.maker]"
                        let _60 := mapping_index_access_mapping_address_uint32_of_address(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ cleaned_12)
                        let _61 := mload(add(mload(0x0180), 320))
                        let cleaned_13 := 0
                        cleaned_13 := and(_61, 0xffffffffffffffffffffffffffffffffffffffff)
                        /// @src 0:24137:24178  "isAuthorized[offer.maker][offer.ratifier]"
                        let dataSlot_13 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                        mstore(0, and(cleaned_13, 0xffffffffffffffffffffffffffffffffffffffff))
                        mstore(0x20, /** @src 0:24137:24178  "isAuthorized[offer.maker][offer.ratifier]" */ _60)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        dataSlot_13 := keccak256(0, 0x40)
                        /// @src 0:24137:24178  "isAuthorized[offer.maker][offer.ratifier]"
                        let value_18 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                        value_18 := and(sload(/** @src 0:24137:24178  "isAuthorized[offer.maker][offer.ratifier]" */ dataSlot_13), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xff)
                        if iszero(value_18)
                        {
                            mstore(0, shl(224, 0xa8d9c8bf))
                            revert(0, 4)
                        }
                        let _62 := mload(add(mload(0x0180), 320))
                        let cleaned_14 := 0
                        cleaned_14 := and(_62, 0xffffffffffffffffffffffffffffffffffffffff)
                        /// @src 0:24221:24246  "IRatifier(offer.ratifier)"
                        let cleaned_15 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                        cleaned_15 := cleaned_14
                        /// @src 0:24221:24257  "IRatifier(offer.ratifier).isRatified"
                        let cleaned_16 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                        cleaned_16 := cleaned_14
                        /// @src 0:24221:24285  "IRatifier(offer.ratifier).isRatified(offer, ratifierData, taker)"
                        let _63 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                        /// @src 0:24221:24285  "IRatifier(offer.ratifier).isRatified(offer, ratifierData, taker)"
                        mstore(_63, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(225, 0x111e276b))
                        /// @src 0:24221:24285  "IRatifier(offer.ratifier).isRatified(offer, ratifierData, taker)"
                        let tail_3 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                        mstore(/** @src 0:24221:24285  "IRatifier(offer.ratifier).isRatified(offer, ratifierData, taker)" */ add(_63, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 4), 96)
                        let tail_4 := abi_encode_struct_Offer(mload(0x0180), add(/** @src 0:24221:24285  "IRatifier(offer.ratifier).isRatified(offer, ratifierData, taker)" */ _63, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 100))
                        mstore(add(/** @src 0:24221:24285  "IRatifier(offer.ratifier).isRatified(offer, ratifierData, taker)" */ _63, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 36), add(sub(tail_4, /** @src 0:24221:24285  "IRatifier(offer.ratifier).isRatified(offer, ratifierData, taker)" */ _63), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(3)))
                        tail_3 := abi_encode_bytes(value1_2, tail_4)
                        mstore(add(/** @src 0:24221:24285  "IRatifier(offer.ratifier).isRatified(offer, ratifierData, taker)" */ _63, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 68), and(/** @src 0:23215:23234  "taker == msg.sender" */ mload(0x0220), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                        /// @src 0:24221:24285  "IRatifier(offer.ratifier).isRatified(offer, ratifierData, taker)"
                        let _64 := staticcall(gas(), cleaned_14, _63, sub(tail_3, _63), _63, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32)
                        /// @src 0:24221:24285  "IRatifier(offer.ratifier).isRatified(offer, ratifierData, taker)"
                        if iszero(_64)
                        {
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let pos_3 := mload(64)
                            returndatacopy(pos_3, 0, returndatasize())
                            revert(pos_3, returndatasize())
                        }
                        /// @src 0:24221:24285  "IRatifier(offer.ratifier).isRatified(offer, ratifierData, taker)"
                        let expr_12 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                        /// @src 0:24221:24285  "IRatifier(offer.ratifier).isRatified(offer, ratifierData, taker)"
                        if _64
                        {
                            let _65 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32
                            /// @src 0:24221:24285  "IRatifier(offer.ratifier).isRatified(offer, ratifierData, taker)"
                            if gt(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32, /** @src 0:24221:24285  "IRatifier(offer.ratifier).isRatified(offer, ratifierData, taker)" */ returndatasize()) { _65 := returndatasize() }
                            finalize_allocation(_63, _65)
                            let value0_10 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                            if slt(sub(/** @src 0:24221:24285  "IRatifier(offer.ratifier).isRatified(offer, ratifierData, taker)" */ add(_63, _65), _63), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32) { revert(0, 0) }
                            value0_10 := mload(/** @src 0:24221:24285  "IRatifier(offer.ratifier).isRatified(offer, ratifierData, taker)" */ _63)
                            expr_12 := value0_10
                        }
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        if iszero(/** @src 0:24221:24305  "IRatifier(offer.ratifier).isRatified(offer, ratifierData, taker) == CALLBACK_SUCCESS" */ eq(expr_12, /** @src 7:1030:1074  "keccak256(\"morpho.midnight.callbackSuccess\")" */ 0x7f87788ea698181ea4d28d1576d0ba4fc92c0dbe5bf75b43692af2ce91dbaea2))
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        {
                            mstore(0, shl(224, 0x882a980f))
                            revert(0, 4)
                        }
                        /// @src 7:234:238  "1e36"
                        let _66 := mload(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ add(mload(0x0180), 160))
                        /// @src 0:24356:24387  "TickLib.tickToPrice(offer.tick)"
                        let var := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                        /// @src 11:214:218  "6744"
                        if /** @src 11:2031:2047  "tick <= MAX_TICK" */ gt(_66, /** @src 11:214:218  "6744" */ 0x1a58)
                        {
                            mstore(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0, /** @src 11:214:218  "6744" */ shl(224, 0xc7e13a01))
                            revert(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0, 4)
                        }
                        /// @src 11:2232:2295  "wExp(LN_ONE_PLUS_DELTA * (int256(MAX_TICK / 2) - int256(tick)))"
                        let _67 := fun_wExp(/** @src 11:134:157  "0.004987541511039073e18" */ mul(0x11b82480116861, sub(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 3372, /** @src 11:2281:2293  "int256(tick)" */ _66)))
                        /// @src 11:2169:2296  "uint256(1e36)..."
                        let var_1 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                        /// @src 11:725:753  "return (x + (d - 1) / 2) / d"
                        var_1 := /** @src 11:732:753  "(x + (d - 1) / 2) / d" */ checked_div_uint256(/** @src 11:134:157  "0.004987541511039073e18" */ add(/** @src 11:2177:2181  "1e36" */ 0xc097ce7bc90715b34b9f1000000000, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shr(/** @src 0:23384:23395  "marketState" */ 0x01, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ add(/** @src 11:134:157  "0.004987541511039073e18" */ _67, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x0de0b6b3a763ffff))), /** @src 11:134:157  "0.004987541511039073e18" */ add(/** @src 11:2225:2229  "1e18" */ 0x0de0b6b3a7640000, /** @src 11:134:157  "0.004987541511039073e18" */ _67))
                        /// @src 11:2169:2359  "uint256(1e36)..."
                        let var_2 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                        /// @src 11:732:753  "(x + (d - 1) / 2) / d"
                        let r := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                        mstore(0x0320, 0)
                        r := div(/** @src 11:134:157  "0.004987541511039073e18" */ add(var_1, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x0ba43b73ff), /** @src 11:371:375  "1e11" */ 0x174876e800)
                        /// @src 11:725:753  "return (x + (d - 1) / 2) / d"
                        var_2 := r
                        /// @src 11:2162:2381  "return uint256(1e36)..."
                        var := /** @src 11:371:375  "1e11" */ mul(r, 0x174876e800)
                        /// @src 7:234:238  "1e36"
                        let _68 := mload(/** @src 0:24444:24465  "offer.market.maturity" */ add(/** @src 0:24444:24456  "offer.market" */ mload(mload(0x0180)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 128))
                        /// @src 0:24422:24483  "UtilsLib.zeroFloorSub(offer.market.maturity, block.timestamp)"
                        let var_z := /** @src -1:-1:-1 */ 0
                        /// @src 12:429:491  "assembly {..."
                        var_z := mul(gt(_68, /** @src 0:23776:23791  "block.timestamp" */ timestamp()), /** @src 12:429:491  "assembly {..." */ sub(_68, /** @src 0:23776:23791  "block.timestamp" */ timestamp()))
                        /// @src 0:24518:24551  "settlementFee(id, timeToMaturity)"
                        let expr_13 := fun_settlementFee(mload(0x0200), var_z)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let _69 := mload(add(mload(0x0180), 32))
                        let cleaned_17 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        cleaned_17 := iszero(iszero(_69))
                        /// @src 0:24583:24635  "offer.buy ? offerPrice - _settlementFee : offerPrice"
                        let expr_14 := /** @src -1:-1:-1 */ 0
                        /// @src 0:24583:24635  "offer.buy ? offerPrice - _settlementFee : offerPrice"
                        switch cleaned_17
                        case 0 { expr_14 := var }
                        default {
                            expr_14 := /** @src 0:24595:24622  "offerPrice - _settlementFee" */ checked_sub_uint256(var, expr_13)
                        }
                        /// @src 0:24666:24694  "sellerPrice + _settlementFee"
                        let expr_15 := checked_add_uint256(expr_14, expr_13)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let _70 := mload(add(mload(0x0180), 32))
                        let cleaned_18 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        cleaned_18 := iszero(iszero(_70))
                        /// @src 0:24726:24805  "offer.buy ? units.mulDivDown(buyerPrice, WAD) : units.mulDivUp(buyerPrice, WAD)"
                        mstore(0x0100, /** @src -1:-1:-1 */ 0)
                        /// @src 0:24726:24805  "offer.buy ? units.mulDivDown(buyerPrice, WAD) : units.mulDivUp(buyerPrice, WAD)"
                        switch cleaned_18
                        case 0 {
                            mstore(0x0100, /** @src 0:24774:24805  "units.mulDivUp(buyerPrice, WAD)" */ fun_mulDivUp_44146(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(68), /** @src 0:24774:24805  "units.mulDivUp(buyerPrice, WAD)" */ expr_15))
                        }
                        default /// @src 0:24726:24805  "offer.buy ? units.mulDivDown(buyerPrice, WAD) : units.mulDivUp(buyerPrice, WAD)"
                        {
                            /// @src 12:653:658  "x * y"
                            let _71 := checked_mul_uint256(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(68), /** @src 0:24738:24771  "units.mulDivDown(buyerPrice, WAD)" */ expr_15)
                            /// @src 12:652:663  "(x * y) / d"
                            let r_1 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let _72 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            _72 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            r_1 := div(_71, /** @src 11:2225:2229  "1e18" */ 0x0de0b6b3a7640000)
                            /// @src 0:24726:24805  "offer.buy ? units.mulDivDown(buyerPrice, WAD) : units.mulDivUp(buyerPrice, WAD)"
                            mstore(0x0100, r_1)
                        }
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let _73 := mload(add(mload(0x0180), 32))
                        let cleaned_19 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        cleaned_19 := iszero(iszero(_73))
                        /// @src 0:24838:24919  "offer.buy ? units.mulDivDown(sellerPrice, WAD) : units.mulDivUp(sellerPrice, WAD)"
                        mstore(0x01a0, /** @src -1:-1:-1 */ 0)
                        /// @src 0:24838:24919  "offer.buy ? units.mulDivDown(sellerPrice, WAD) : units.mulDivUp(sellerPrice, WAD)"
                        switch cleaned_19
                        case 0 {
                            mstore(0x01a0, /** @src 0:24887:24919  "units.mulDivUp(sellerPrice, WAD)" */ fun_mulDivUp_44146(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(68), /** @src 0:24887:24919  "units.mulDivUp(sellerPrice, WAD)" */ expr_14))
                        }
                        default /// @src 0:24838:24919  "offer.buy ? units.mulDivDown(sellerPrice, WAD) : units.mulDivUp(sellerPrice, WAD)"
                        {
                            /// @src 12:653:658  "x * y"
                            let _74 := checked_mul_uint256(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(68), /** @src 0:24850:24884  "units.mulDivDown(sellerPrice, WAD)" */ expr_14)
                            /// @src 12:652:663  "(x * y) / d"
                            let r_2 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let _75 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            _75 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            r_2 := div(_74, /** @src 11:2225:2229  "1e18" */ 0x0de0b6b3a7640000)
                            /// @src 0:24838:24919  "offer.buy ? units.mulDivDown(sellerPrice, WAD) : units.mulDivUp(sellerPrice, WAD)"
                            mstore(0x01a0, r_2)
                        }
                        /// @src 0:24930:24949  "uint256 newConsumed"
                        mstore(0x01e0, /** @src -1:-1:-1 */ 0)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let _76 := mload(add(mload(0x0180), 416))
                        let cleaned_20 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        cleaned_20 := and(_76, 0xffffffffffffffffffffffffffffffff)
                        /// @src 0:24963:24982  "offer.maxAssets > 0"
                        let cleaned_21 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        cleaned_21 := cleaned_20
                        /// @src 0:24959:25327  "if (offer.maxAssets > 0) {..."
                        switch /** @src 0:24963:24982  "offer.maxAssets > 0" */ iszero(iszero(cleaned_20))
                        case /** @src 0:24959:25327  "if (offer.maxAssets > 0) {..." */ 0 {
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let _77 := mload(add(mload(0x0180), 64))
                            let cleaned_22 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            cleaned_22 := and(_77, 0xffffffffffffffffffffffffffffffffffffffff)
                            /// @src 0:25205:25226  "consumed[offer.maker]"
                            let _78 := mapping_index_access_mapping_address__uint32__of_address(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ cleaned_22)
                            let _79 := mload(add(mload(0x0180), 192))
                            /// @src 0:25205:25239  "consumed[offer.maker][offer.group]"
                            let dataSlot_14 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _79)
                            mstore(32, _78)
                            dataSlot_14 := keccak256(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 64)
                            /// @src 0:25205:25239  "consumed[offer.maker][offer.group]"
                            let value_19 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            value_19 := and(sload(dataSlot_14), 0xffffffffffffffffffffffffffffffff)
                            /// @src 0:25205:25247  "consumed[offer.maker][offer.group] + units"
                            let cleaned_23 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            cleaned_23 := value_19
                            /// @src 0:25191:25247  "newConsumed = consumed[offer.maker][offer.group] + units"
                            mstore(0x01e0, /** @src 0:25205:25247  "consumed[offer.maker][offer.group] + units" */ checked_add_uint256(value_19, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(68)))
                            let _80 := mload(add(mload(0x0180), 384))
                            let cleaned_24 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            cleaned_24 := and(_80, 0xffffffffffffffffffffffffffffffff)
                            /// @src 0:25269:25298  "newConsumed <= offer.maxUnits"
                            let cleaned_25 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            cleaned_25 := cleaned_24
                            if /** @src 0:25269:25298  "newConsumed <= offer.maxUnits" */ gt(mload(0x01e0), cleaned_24)
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            {
                                mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(224, 0xe7a700db))
                                revert(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 4)
                            }
                        }
                        default /// @src 0:24959:25327  "if (offer.maxAssets > 0) {..."
                        {
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let _81 := mload(add(mload(0x0180), 64))
                            let cleaned_26 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            cleaned_26 := and(_81, 0xffffffffffffffffffffffffffffffffffffffff)
                            /// @src 0:25012:25033  "consumed[offer.maker]"
                            let _82 := mapping_index_access_mapping_address__uint32__of_address(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ cleaned_26)
                            let _83 := mload(add(mload(0x0180), 192))
                            /// @src 0:25012:25046  "consumed[offer.maker][offer.group]"
                            let dataSlot_15 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _83)
                            mstore(32, _82)
                            dataSlot_15 := keccak256(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 64)
                            /// @src 0:25012:25046  "consumed[offer.maker][offer.group]"
                            let value_20 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            value_20 := and(sload(dataSlot_15), 0xffffffffffffffffffffffffffffffff)
                            let _84 := mload(add(mload(0x0180), 32))
                            let cleaned_27 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            cleaned_27 := iszero(iszero(_84))
                            /// @src 0:25050:25088  "offer.buy ? buyerAssets : sellerAssets"
                            let expr_16 := /** @src -1:-1:-1 */ 0
                            /// @src 0:25050:25088  "offer.buy ? buyerAssets : sellerAssets"
                            switch cleaned_27
                            case 0 { expr_16 := mload(0x01a0) }
                            default { expr_16 := mload(0x0100) }
                            /// @src 0:24998:25089  "newConsumed = consumed[offer.maker][offer.group] + (offer.buy ? buyerAssets : sellerAssets)"
                            mstore(0x01e0, /** @src 0:25012:25089  "consumed[offer.maker][offer.group] + (offer.buy ? buyerAssets : sellerAssets)" */ checked_add_uint256(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ value_20, /** @src 0:25012:25089  "consumed[offer.maker][offer.group] + (offer.buy ? buyerAssets : sellerAssets)" */ expr_16))
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let _85 := mload(add(mload(0x0180), 416))
                            let cleaned_28 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            cleaned_28 := and(_85, 0xffffffffffffffffffffffffffffffff)
                            /// @src 0:25111:25141  "newConsumed <= offer.maxAssets"
                            let cleaned_29 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            cleaned_29 := cleaned_28
                            if /** @src 0:25111:25141  "newConsumed <= offer.maxAssets" */ gt(mload(0x01e0), cleaned_28)
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            {
                                mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(224, 0x22b950bf))
                                revert(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 4)
                            }
                        }
                        let _86 := mload(add(mload(0x0180), 32))
                        let cleaned_30 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        cleaned_30 := iszero(iszero(_86))
                        /// @src 0:25371:25426  "offer.buy ? (offer.maker, taker) : (taker, offer.maker)"
                        mstore(0x0240, /** @src -1:-1:-1 */ 0)
                        mstore(0x01c0, 0)
                        /// @src 0:25371:25426  "offer.buy ? (offer.maker, taker) : (taker, offer.maker)"
                        switch cleaned_30
                        case 0 {
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let _87 := mload(add(mload(0x0180), 64))
                            let cleaned_31 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            cleaned_31 := and(_87, 0xffffffffffffffffffffffffffffffffffffffff)
                            /// @src 0:25371:25426  "offer.buy ? (offer.maker, taker) : (taker, offer.maker)"
                            mstore(0x0240, mload(0x0220))
                            mstore(0x01c0, cleaned_31)
                        }
                        default {
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let _88 := mload(add(mload(0x0180), 64))
                            let cleaned_32 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            cleaned_32 := and(_88, 0xffffffffffffffffffffffffffffffffffffffff)
                            /// @src 0:25371:25426  "offer.buy ? (offer.maker, taker) : (taker, offer.maker)"
                            mstore(0x0240, cleaned_32)
                            mstore(0x01c0, mload(0x0220))
                        }
                        /// @src 0:25464:25476  "position[id]"
                        let dataSlot_16 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x0200))
                        mstore(32, /** @src -1:-1:-1 */ 0)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        dataSlot_16 := keccak256(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 64)
                        /// @src 0:25464:25483  "position[id][buyer]"
                        let dataSlot_17 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:25464:25483  "position[id][buyer]" */ mload(0x0240), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                        mstore(0x20, /** @src 0:25464:25476  "position[id]" */ dataSlot_16)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        dataSlot_17 := keccak256(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x40)
                        /// @src 0:25522:25534  "position[id]"
                        let dataSlot_18 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x0200))
                        mstore(32, /** @src -1:-1:-1 */ 0)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        dataSlot_18 := keccak256(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 64)
                        /// @src 0:25522:25542  "position[id][seller]"
                        let dataSlot_19 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:25522:25542  "position[id][seller]" */ mload(0x01c0), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                        mstore(0x20, /** @src 0:25522:25534  "position[id]" */ dataSlot_18)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        dataSlot_19 := keccak256(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x40)
                        /// @src 0:25557:25602  "hasCredit(id, buyer) || units > buyerPos.debt"
                        let expr_17 := /** @src 0:25557:25577  "hasCredit(id, buyer)" */ fun_hasCredit(mload(0x0200), mload(0x0240))
                        /// @src 0:25557:25602  "hasCredit(id, buyer) || units > buyerPos.debt"
                        if iszero(expr_17)
                        {
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let _89 := sload(/** @src 0:25589:25602  "buyerPos.debt" */ add(dataSlot_17, /** @src 0:23593:23619  "_marketState.continuousFee" */ 2))
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let cleaned_33 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            cleaned_33 := and(_89, 0xffffffffffffffffffffffffffffffff)
                            /// @src 0:25581:25602  "units > buyerPos.debt"
                            let cleaned_34 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            cleaned_34 := cleaned_33
                            /// @src 0:25557:25602  "hasCredit(id, buyer) || units > buyerPos.debt"
                            expr_17 := /** @src 0:25581:25602  "units > buyerPos.debt" */ gt(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(68), /** @src 0:25581:25602  "units > buyerPos.debt" */ cleaned_33)
                        }
                        /// @src 0:25553:25644  "if (hasCredit(id, buyer) || units > buyerPos.debt) _updatePosition(offer.market, id, buyer)"
                        if expr_17
                        {
                            /// @src 0:25604:25644  "_updatePosition(offer.market, id, buyer)"
                            let expr_component_3, expr_component_4, expr_component_5 := fun_updatePosition(/** @src 0:25620:25632  "offer.market" */ mload(mload(0x0180)), /** @src 0:25604:25644  "_updatePosition(offer.market, id, buyer)" */ mload(0x0200), mload(0x0240))
                        }
                        /// @src 0:25654:25722  "if (hasCredit(id, seller)) _updatePosition(offer.market, id, seller)"
                        if /** @src 0:25658:25679  "hasCredit(id, seller)" */ fun_hasCredit(mload(0x0200), mload(0x01c0))
                        /// @src 0:25654:25722  "if (hasCredit(id, seller)) _updatePosition(offer.market, id, seller)"
                        {
                            /// @src 0:25681:25722  "_updatePosition(offer.market, id, seller)"
                            let expr_component_6, expr_component_7, expr_component_8 := fun_updatePosition(/** @src 0:25697:25709  "offer.market" */ mload(mload(0x0180)), /** @src 0:25681:25722  "_updatePosition(offer.market, id, seller)" */ mload(0x0200), mload(0x01c0))
                        }
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let _90 := sload(/** @src 0:25792:25805  "buyerPos.debt" */ add(dataSlot_17, /** @src 0:23593:23619  "_marketState.continuousFee" */ 2))
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let cleaned_35 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        cleaned_35 := and(_90, 0xffffffffffffffffffffffffffffffff)
                        /// @src 0:25763:25806  "UtilsLib.zeroFloorSub(units, buyerPos.debt)"
                        let cleaned_36 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        cleaned_36 := cleaned_35
                        /// @src 0:25763:25806  "UtilsLib.zeroFloorSub(units, buyerPos.debt)"
                        let var_z_1 := /** @src -1:-1:-1 */ 0
                        /// @src 12:429:491  "assembly {..."
                        var_z_1 := mul(gt(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(68), /** @src 12:429:491  "assembly {..." */ cleaned_35), sub(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(68), /** @src 12:429:491  "assembly {..." */ cleaned_35))
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(0x0160, sload(/** @src 0:25867:25883  "sellerPos.credit" */ dataSlot_19))
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let cleaned_37 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        cleaned_37 := and(mload(0x0160), 0xffffffffffffffffffffffffffffffff)
                        /// @src 0:25847:25884  "UtilsLib.min(units, sellerPos.credit)"
                        let cleaned_38 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        cleaned_38 := cleaned_37
                        /// @src 0:25847:25884  "UtilsLib.min(units, sellerPos.credit)"
                        let var_z_2 := /** @src -1:-1:-1 */ 0
                        /// @src 12:259:329  "assembly {..."
                        var_z_2 := xor(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(68), /** @src 12:259:329  "assembly {..." */ mul(xor(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(68), /** @src 12:259:329  "assembly {..." */ cleaned_37), lt(cleaned_37, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(68))))
                        /// @src 0:25923:25951  "units - sellerCreditDecrease"
                        let expr_18 := checked_sub_uint256(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(68), /** @src 0:25923:25951  "units - sellerCreditDecrease" */ var_z_2)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let _91 := sload(/** @src 0:23593:23619  "_marketState.continuousFee" */ add(dataSlot_12, 2))
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let value_21 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        value_21 := and(shr(112, _91), 0xffffffff)
                        /// @src 0:26057:26100  "_marketState.continuousFee * timeToMaturity"
                        let converted := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        converted := value_21
                        /// @src 12:653:658  "x * y"
                        let _92 := checked_mul_uint256(/** @src 0:26026:26106  "buyerCreditIncrease.mulDivDown(_marketState.continuousFee * timeToMaturity, WAD)" */ var_z_1, /** @src 0:26057:26100  "_marketState.continuousFee * timeToMaturity" */ checked_mul_uint256(value_21, var_z))
                        /// @src 12:652:663  "(x * y) / d"
                        let r_3 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let _93 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        _93 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        r_3 := div(_92, /** @src 11:2225:2229  "1e18" */ 0x0de0b6b3a7640000)
                        /// @src 0:26007:26107  "UtilsLib.toUint128(buyerCreditIncrease.mulDivDown(_marketState.continuousFee * timeToMaturity, WAD))"
                        mstore(0xe0, fun_toUint128(/** @src 12:652:663  "(x * y) / d" */ r_3))
                        /// @src 0:26152:26292  "sellerPos.credit > 0..."
                        mstore(0xa0, /** @src -1:-1:-1 */ 0)
                        /// @src 0:26152:26292  "sellerPos.credit > 0..."
                        switch /** @src 0:26152:26172  "sellerPos.credit > 0" */ iszero(iszero(cleaned_37))
                        case /** @src 0:26152:26292  "sellerPos.credit > 0..." */ 0 {
                            mstore(0xa0, /** @src -1:-1:-1 */ 0)
                        }
                        default /// @src 0:26152:26292  "sellerPos.credit > 0..."
                        {
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let value_22 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            value_22 := shr(128, mload(0x0160))
                            /// @src 0:26206:26235  "sellerPos.pendingFee.mulDivUp"
                            let cleaned_39 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            cleaned_39 := value_22
                            /// @src 0:26152:26292  "sellerPos.credit > 0..."
                            mstore(0xa0, /** @src 0:26187:26276  "UtilsLib.toUint128(sellerPos.pendingFee.mulDivUp(sellerCreditDecrease, sellerPos.credit))" */ fun_toUint128(/** @src 0:26206:26275  "sellerPos.pendingFee.mulDivUp(sellerCreditDecrease, sellerPos.credit)" */ fun_mulDivUp(value_22, var_z_2, cleaned_37)))
                        }
                        /// @src 0:26311:26351  "block.timestamp <= offer.market.maturity"
                        let _94 := gt(/** @src 0:23776:23791  "block.timestamp" */ timestamp(), /** @src 7:234:238  "1e36" */ mload(/** @src 0:26330:26351  "offer.market.maturity" */ add(/** @src 0:26330:26342  "offer.market" */ mload(mload(0x0180)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 128)))
                        /// @src 0:26311:26378  "block.timestamp <= offer.market.maturity || sellerDebtIncrease == 0"
                        let expr_19 := /** @src 0:26311:26351  "block.timestamp <= offer.market.maturity" */ iszero(_94)
                        /// @src 0:26311:26378  "block.timestamp <= offer.market.maturity || sellerDebtIncrease == 0"
                        if _94
                        {
                            expr_19 := /** @src 0:26355:26378  "sellerDebtIncrease == 0" */ iszero(expr_18)
                        }
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        if iszero(expr_19)
                        {
                            mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(225, 0x721fce31))
                            revert(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 4)
                        }
                        let _95 := mload(add(mload(0x0180), 352))
                        let cleaned_40 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let _96 := iszero(_95)
                        cleaned_40 := iszero(_96)
                        /// @src 0:26444:26461  "!offer.reduceOnly"
                        let cleaned_41 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        cleaned_41 := _96
                        /// @src 0:26444:26529  "!offer.reduceOnly || (offer.buy ? buyerCreditIncrease == 0 : sellerDebtIncrease == 0)"
                        let expr_20 := _96
                        if cleaned_40
                        {
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let _97 := mload(add(mload(0x0180), 32))
                            let cleaned_42 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            cleaned_42 := iszero(iszero(_97))
                            /// @src 0:26466:26528  "offer.buy ? buyerCreditIncrease == 0 : sellerDebtIncrease == 0"
                            let expr_21 := /** @src -1:-1:-1 */ 0
                            /// @src 0:26466:26528  "offer.buy ? buyerCreditIncrease == 0 : sellerDebtIncrease == 0"
                            switch cleaned_42
                            case 0 {
                                expr_21 := /** @src 0:26505:26528  "sellerDebtIncrease == 0" */ iszero(expr_18)
                            }
                            default /// @src 0:26466:26528  "offer.buy ? buyerCreditIncrease == 0 : sellerDebtIncrease == 0"
                            {
                                expr_21 := /** @src 0:26478:26502  "buyerCreditIncrease == 0" */ iszero(var_z_1)
                            }
                            /// @src 0:26444:26529  "!offer.reduceOnly || (offer.buy ? buyerCreditIncrease == 0 : sellerDebtIncrease == 0)"
                            expr_20 := expr_21
                        }
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        if iszero(expr_20)
                        {
                            mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(226, 0x263738af))
                            revert(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 4)
                        }
                        let _98 := mload(/** @src 0:26612:26634  "offer.market.enterGate" */ add(/** @src 0:26612:26624  "offer.market" */ mload(mload(0x0180)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 192))
                        let cleaned_43 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        cleaned_43 := and(_98, 0xffffffffffffffffffffffffffffffffffffffff)
                        /// @src 0:26612:26676  "offer.market.enterGate == address(0) || buyerCreditIncrease == 0"
                        let expr_22 := /** @src 0:26612:26648  "offer.market.enterGate == address(0)" */ iszero(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ cleaned_43)
                        /// @src 0:26612:26676  "offer.market.enterGate == address(0) || buyerCreditIncrease == 0"
                        if iszero(expr_22)
                        {
                            expr_22 := /** @src 0:26652:26676  "buyerCreditIncrease == 0" */ iszero(var_z_1)
                        }
                        /// @src 0:26612:26755  "offer.market.enterGate == address(0) || buyerCreditIncrease == 0..."
                        let expr_23 := expr_22
                        if iszero(expr_22)
                        {
                            /// @src 0:26696:26730  "IEnterGate(offer.market.enterGate)"
                            let cleaned_44 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            cleaned_44 := cleaned_43
                            /// @src 0:26696:26748  "IEnterGate(offer.market.enterGate).canIncreaseCredit"
                            let cleaned_45 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            cleaned_45 := cleaned_43
                            /// @src 0:26696:26755  "IEnterGate(offer.market.enterGate).canIncreaseCredit(buyer)"
                            let _99 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                            /// @src 0:26696:26755  "IEnterGate(offer.market.enterGate).canIncreaseCredit(buyer)"
                            mstore(_99, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(225, 0x2c564fcf))
                            /// @src 0:26696:26755  "IEnterGate(offer.market.enterGate).canIncreaseCredit(buyer)"
                            let tail_5 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            tail_5 := add(/** @src 0:26696:26755  "IEnterGate(offer.market.enterGate).canIncreaseCredit(buyer)" */ _99, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 36)
                            mstore(/** @src 0:26696:26755  "IEnterGate(offer.market.enterGate).canIncreaseCredit(buyer)" */ add(_99, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 4), and(mload(0x0240), 0xffffffffffffffffffffffffffffffffffffffff))
                            /// @src 0:26696:26755  "IEnterGate(offer.market.enterGate).canIncreaseCredit(buyer)"
                            let _100 := staticcall(gas(), cleaned_43, _99, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 36, /** @src 0:26696:26755  "IEnterGate(offer.market.enterGate).canIncreaseCredit(buyer)" */ _99, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32)
                            /// @src 0:26696:26755  "IEnterGate(offer.market.enterGate).canIncreaseCredit(buyer)"
                            if iszero(_100)
                            {
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                let pos_4 := mload(64)
                                returndatacopy(pos_4, /** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ returndatasize())
                                revert(pos_4, returndatasize())
                            }
                            /// @src 0:26696:26755  "IEnterGate(offer.market.enterGate).canIncreaseCredit(buyer)"
                            let expr_24 := /** @src -1:-1:-1 */ 0
                            /// @src 0:26696:26755  "IEnterGate(offer.market.enterGate).canIncreaseCredit(buyer)"
                            if _100
                            {
                                let _101 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32
                                /// @src 0:26696:26755  "IEnterGate(offer.market.enterGate).canIncreaseCredit(buyer)"
                                if gt(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32, /** @src 0:26696:26755  "IEnterGate(offer.market.enterGate).canIncreaseCredit(buyer)" */ returndatasize()) { _101 := returndatasize() }
                                finalize_allocation(_99, _101)
                                expr_24 := abi_decode_bool_fromMemory(_99, add(_99, _101))
                            }
                            /// @src 0:26612:26755  "offer.market.enterGate == address(0) || buyerCreditIncrease == 0..."
                            expr_23 := expr_24
                        }
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        if iszero(expr_23)
                        {
                            mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(224, 0x71a4e09b))
                            revert(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 4)
                        }
                        let _102 := mload(/** @src 0:26842:26864  "offer.market.enterGate" */ add(/** @src 0:26842:26854  "offer.market" */ mload(mload(0x0180)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 192))
                        let cleaned_46 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        cleaned_46 := and(_102, 0xffffffffffffffffffffffffffffffffffffffff)
                        /// @src 0:26842:26878  "offer.market.enterGate == address(0)"
                        let cleaned_47 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        cleaned_47 := cleaned_46
                        /// @src 0:26842:26905  "offer.market.enterGate == address(0) || sellerDebtIncrease == 0"
                        let expr_25 := /** @src 0:26842:26878  "offer.market.enterGate == address(0)" */ iszero(cleaned_46)
                        /// @src 0:26842:26905  "offer.market.enterGate == address(0) || sellerDebtIncrease == 0"
                        if iszero(expr_25)
                        {
                            expr_25 := /** @src 0:26882:26905  "sellerDebtIncrease == 0" */ iszero(expr_18)
                        }
                        /// @src 0:26842:26983  "offer.market.enterGate == address(0) || sellerDebtIncrease == 0..."
                        let expr_26 := expr_25
                        if iszero(expr_25)
                        {
                            /// @src 0:26925:26959  "IEnterGate(offer.market.enterGate)"
                            let cleaned_48 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            cleaned_48 := cleaned_46
                            /// @src 0:26925:26975  "IEnterGate(offer.market.enterGate).canIncreaseDebt"
                            let cleaned_49 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            cleaned_49 := cleaned_46
                            /// @src 0:26925:26983  "IEnterGate(offer.market.enterGate).canIncreaseDebt(seller)"
                            let _103 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                            /// @src 0:26925:26983  "IEnterGate(offer.market.enterGate).canIncreaseDebt(seller)"
                            mstore(_103, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(225, 0x7f4dfcab))
                            /// @src 0:26925:26983  "IEnterGate(offer.market.enterGate).canIncreaseDebt(seller)"
                            let tail_6 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            tail_6 := add(/** @src 0:26925:26983  "IEnterGate(offer.market.enterGate).canIncreaseDebt(seller)" */ _103, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 36)
                            mstore(/** @src 0:26925:26983  "IEnterGate(offer.market.enterGate).canIncreaseDebt(seller)" */ add(_103, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 4), and(mload(0x01c0), 0xffffffffffffffffffffffffffffffffffffffff))
                            /// @src 0:26925:26983  "IEnterGate(offer.market.enterGate).canIncreaseDebt(seller)"
                            let _104 := staticcall(gas(), cleaned_46, _103, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 36, /** @src 0:26925:26983  "IEnterGate(offer.market.enterGate).canIncreaseDebt(seller)" */ _103, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32)
                            /// @src 0:26925:26983  "IEnterGate(offer.market.enterGate).canIncreaseDebt(seller)"
                            if iszero(_104)
                            {
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                let pos_5 := mload(64)
                                returndatacopy(pos_5, /** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ returndatasize())
                                revert(pos_5, returndatasize())
                            }
                            /// @src 0:26925:26983  "IEnterGate(offer.market.enterGate).canIncreaseDebt(seller)"
                            let expr_27 := /** @src -1:-1:-1 */ 0
                            /// @src 0:26925:26983  "IEnterGate(offer.market.enterGate).canIncreaseDebt(seller)"
                            if _104
                            {
                                let _105 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32
                                /// @src 0:26925:26983  "IEnterGate(offer.market.enterGate).canIncreaseDebt(seller)"
                                if gt(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32, /** @src 0:26925:26983  "IEnterGate(offer.market.enterGate).canIncreaseDebt(seller)" */ returndatasize()) { _105 := returndatasize() }
                                finalize_allocation(_103, _105)
                                expr_27 := abi_decode_bool_fromMemory(_103, add(_103, _105))
                            }
                            /// @src 0:26842:26983  "offer.market.enterGate == address(0) || sellerDebtIncrease == 0..."
                            expr_26 := expr_27
                        }
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        if iszero(expr_26)
                        {
                            mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(226, 0x38b531db))
                            revert(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 4)
                        }
                        sstore(/** @src 0:25792:25805  "buyerPos.debt" */ add(dataSlot_17, /** @src 0:23593:23619  "_marketState.continuousFee" */ 2), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ or(and(sload(/** @src 0:25792:25805  "buyerPos.debt" */ add(dataSlot_17, /** @src 0:23593:23619  "_marketState.continuousFee" */ 2)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(0xffffffffffffffffffffffffffffffff)), and(/** @src 0:27049:27113  "buyerPos.debt -= UtilsLib.toUint128(units - buyerCreditIncrease)" */ checked_sub_uint128(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ cleaned_35, /** @src 0:27066:27113  "UtilsLib.toUint128(units - buyerCreditIncrease)" */ fun_toUint128(/** @src 0:27085:27112  "units - buyerCreditIncrease" */ checked_sub_uint256(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(68), /** @src 0:27085:27112  "units - buyerCreditIncrease" */ var_z_1))), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)))
                        let _106 := sload(/** @src 0:27123:27169  "buyerPos.pendingFee += buyerPendingFeeIncrease" */ dataSlot_17)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let value_23 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        value_23 := shr(128, _106)
                        /// @src 0:27123:27169  "buyerPos.pendingFee += buyerPendingFeeIncrease"
                        update_storage_value_offset_uint128_to_uint128(dataSlot_17, checked_add_uint128(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ value_23, /** @src 0:27123:27169  "buyerPos.pendingFee += buyerPendingFeeIncrease" */ mload(0xe0)))
                        /// @src 0:27198:27237  "UtilsLib.toUint128(buyerCreditIncrease)"
                        let _107 := fun_toUint128(var_z_1)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let _108 := sload(/** @src 0:27179:27237  "buyerPos.credit += UtilsLib.toUint128(buyerCreditIncrease)" */ dataSlot_17)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let cleaned_50 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        cleaned_50 := and(_108, 0xffffffffffffffffffffffffffffffff)
                        sstore(/** @src 0:27179:27237  "buyerPos.credit += UtilsLib.toUint128(buyerCreditIncrease)" */ dataSlot_17, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ or(and(sload(/** @src 0:27179:27237  "buyerPos.credit += UtilsLib.toUint128(buyerCreditIncrease)" */ dataSlot_17), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(0xffffffffffffffffffffffffffffffff)), and(/** @src 0:27179:27237  "buyerPos.credit += UtilsLib.toUint128(buyerCreditIncrease)" */ checked_add_uint128(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ cleaned_50, /** @src 0:27198:27237  "UtilsLib.toUint128(buyerCreditIncrease)" */ _107), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)))
                        let _109 := sload(/** @src 0:27248:27296  "sellerPos.pendingFee -= sellerPendingFeeDecrease" */ dataSlot_19)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let value_24 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        value_24 := shr(128, _109)
                        /// @src 0:27248:27296  "sellerPos.pendingFee -= sellerPendingFeeDecrease"
                        update_storage_value_offset_uint128_to_uint128(dataSlot_19, checked_sub_uint128(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ value_24, /** @src 0:27248:27296  "sellerPos.pendingFee -= sellerPendingFeeDecrease" */ mload(0xa0)))
                        /// @src 0:27326:27366  "UtilsLib.toUint128(sellerCreditDecrease)"
                        let _110 := fun_toUint128(var_z_2)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let _111 := sload(/** @src 0:27306:27366  "sellerPos.credit -= UtilsLib.toUint128(sellerCreditDecrease)" */ dataSlot_19)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let cleaned_51 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        cleaned_51 := and(_111, 0xffffffffffffffffffffffffffffffff)
                        sstore(/** @src 0:27306:27366  "sellerPos.credit -= UtilsLib.toUint128(sellerCreditDecrease)" */ dataSlot_19, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ or(and(sload(/** @src 0:27306:27366  "sellerPos.credit -= UtilsLib.toUint128(sellerCreditDecrease)" */ dataSlot_19), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(0xffffffffffffffffffffffffffffffff)), and(/** @src 0:27306:27366  "sellerPos.credit -= UtilsLib.toUint128(sellerCreditDecrease)" */ checked_sub_uint128(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ cleaned_51, /** @src 0:27326:27366  "UtilsLib.toUint128(sellerCreditDecrease)" */ _110), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)))
                        /// @src 0:27394:27432  "UtilsLib.toUint128(sellerDebtIncrease)"
                        let expr_28 := fun_toUint128(expr_18)
                        /// @src 0:27376:27390  "sellerPos.debt"
                        let _112 := add(dataSlot_19, /** @src 0:23593:23619  "_marketState.continuousFee" */ 2)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let _113 := sload(/** @src 0:27376:27432  "sellerPos.debt += UtilsLib.toUint128(sellerDebtIncrease)" */ _112)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let cleaned_52 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        cleaned_52 := and(_113, 0xffffffffffffffffffffffffffffffff)
                        sstore(/** @src 0:27376:27432  "sellerPos.debt += UtilsLib.toUint128(sellerDebtIncrease)" */ _112, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ or(and(sload(/** @src 0:27376:27432  "sellerPos.debt += UtilsLib.toUint128(sellerDebtIncrease)" */ _112), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(0xffffffffffffffffffffffffffffffff)), and(/** @src 0:27376:27432  "sellerPos.debt += UtilsLib.toUint128(sellerDebtIncrease)" */ checked_add_uint128(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ cleaned_52, /** @src 0:27376:27432  "sellerPos.debt += UtilsLib.toUint128(sellerDebtIncrease)" */ expr_28), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)))
                        let _114 := sload(/** @src 0:27500:27523  "_marketState.totalUnits" */ dataSlot_12)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let cleaned_53 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        cleaned_53 := and(_114, 0xffffffffffffffffffffffffffffffff)
                        /// @src 0:27500:27545  "_marketState.totalUnits + buyerCreditIncrease"
                        let cleaned_54 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        cleaned_54 := cleaned_53
                        sstore(/** @src 0:27443:27569  "_marketState.totalUnits =..." */ dataSlot_12, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ or(and(sload(/** @src 0:27443:27569  "_marketState.totalUnits =..." */ dataSlot_12), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(0xffffffffffffffffffffffffffffffff)), and(/** @src 0:27481:27569  "UtilsLib.toUint128(_marketState.totalUnits + buyerCreditIncrease - sellerCreditDecrease)" */ fun_toUint128(/** @src 0:27500:27568  "_marketState.totalUnits + buyerCreditIncrease - sellerCreditDecrease" */ checked_sub_uint256(/** @src 0:27500:27545  "_marketState.totalUnits + buyerCreditIncrease" */ checked_add_uint256(cleaned_53, var_z_1), /** @src 0:27500:27568  "_marketState.totalUnits + buyerCreditIncrease - sellerCreditDecrease" */ var_z_2)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)))
                        /// @src 0:27629:27655  "buyerAssets - sellerAssets"
                        let expr_29 := checked_sub_uint256(mload(0x0100), mload(0x01a0))
                        /// @src 0:27602:27624  "offer.market.loanToken"
                        let _115 := add(/** @src 0:27602:27614  "offer.market" */ mload(mload(0x0180)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 64)
                        /// @src 0:27602:27624  "offer.market.loanToken"
                        let returnValue := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        returnValue := and(mload(_115), 0xffffffffffffffffffffffffffffffffffffffff)
                        /// @src 0:27579:27625  "claimableSettlementFee[offer.market.loanToken]"
                        let dataSlot_20 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ returnValue)
                        mstore(32, /** @src 0:27579:27601  "claimableSettlementFee" */ 0x06)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        dataSlot_20 := keccak256(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 64)
                        sstore(dataSlot_20, /** @src 0:27579:27655  "claimableSettlementFee[offer.market.loanToken] += buyerAssets - sellerAssets" */ checked_add_uint256(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ sload(/** @src 0:27579:27655  "claimableSettlementFee[offer.market.loanToken] += buyerAssets - sellerAssets" */ dataSlot_20), expr_29))
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let _116 := mload(add(mload(0x0180), 64))
                        let cleaned_55 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        cleaned_55 := and(_116, 0xffffffffffffffffffffffffffffffffffffffff)
                        /// @src 0:27765:27786  "consumed[offer.maker]"
                        let _117 := mapping_index_access_mapping_address__uint32__of_address(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ cleaned_55)
                        let _118 := mload(add(mload(0x0180), 192))
                        /// @src 0:27765:27799  "consumed[offer.maker][offer.group]"
                        let dataSlot_21 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _118)
                        mstore(32, _117)
                        dataSlot_21 := keccak256(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 64)
                        sstore(/** @src 0:27765:27799  "consumed[offer.maker][offer.group]" */ dataSlot_21, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ or(and(sload(/** @src 0:27765:27799  "consumed[offer.maker][offer.group]" */ dataSlot_21), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(0xffffffffffffffffffffffffffffffff)), and(and(/** @src 0:27802:27822  "uint128(newConsumed)" */ mload(0x01e0), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff), 0xffffffffffffffffffffffffffffffff)))
                        let _119 := mload(add(mload(0x0180), 32))
                        let cleaned_56 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        cleaned_56 := iszero(iszero(_119))
                        /// @src 0:27857:27899  "offer.buy ? offer.callback : takerCallback"
                        let expr_30 := /** @src -1:-1:-1 */ 0
                        /// @src 0:27857:27899  "offer.buy ? offer.callback : takerCallback"
                        switch cleaned_56
                        case 0 { expr_30 := mload(0xc0) }
                        default {
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let _120 := mload(add(mload(0x0180), 224))
                            let cleaned_57 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            cleaned_57 := and(_120, 0xffffffffffffffffffffffffffffffffffffffff)
                            /// @src 0:27857:27899  "offer.buy ? offer.callback : takerCallback"
                            expr_30 := cleaned_57
                        }
                        /// @src 0:27934:27976  "offer.buy ? takerCallback : offer.callback"
                        let expr_31 := /** @src -1:-1:-1 */ 0
                        /// @src 0:27934:27976  "offer.buy ? takerCallback : offer.callback"
                        switch cleaned_56
                        case 0 {
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let _121 := mload(add(mload(0x0180), 224))
                            let cleaned_58 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            cleaned_58 := and(_121, 0xffffffffffffffffffffffffffffffffffffffff)
                            /// @src 0:27934:27976  "offer.buy ? takerCallback : offer.callback"
                            expr_31 := cleaned_58
                        }
                        default { expr_31 := mload(0xc0) }
                        /// @src 0:28002:28080  "buyerCallback != address(0) ? buyerCallback : (offer.buy ? buyer : msg.sender)"
                        let expr_32 := /** @src -1:-1:-1 */ 0
                        /// @src 0:28002:28080  "buyerCallback != address(0) ? buyerCallback : (offer.buy ? buyer : msg.sender)"
                        switch /** @src 0:28002:28029  "buyerCallback != address(0)" */ iszero(iszero(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:28002:28029  "buyerCallback != address(0)" */ expr_30, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff)))
                        case /** @src 0:28002:28080  "buyerCallback != address(0) ? buyerCallback : (offer.buy ? buyer : msg.sender)" */ 0 {
                            /// @src 0:28049:28079  "offer.buy ? buyer : msg.sender"
                            let expr_33 := /** @src -1:-1:-1 */ 0
                            /// @src 0:28049:28079  "offer.buy ? buyer : msg.sender"
                            switch cleaned_56
                            case 0 {
                                expr_33 := /** @src 0:23224:23234  "msg.sender" */ caller()
                            }
                            default /// @src 0:28049:28079  "offer.buy ? buyer : msg.sender"
                            { expr_33 := mload(0x0240) }
                            /// @src 0:28002:28080  "buyerCallback != address(0) ? buyerCallback : (offer.buy ? buyer : msg.sender)"
                            expr_32 := expr_33
                        }
                        default { expr_32 := expr_30 }
                        /// @src 0:28109:28176  "offer.buy ? receiverIfTakerIsSeller : offer.receiverIfMakerIsSeller"
                        mstore(0x80, /** @src -1:-1:-1 */ 0)
                        /// @src 0:28109:28176  "offer.buy ? receiverIfTakerIsSeller : offer.receiverIfMakerIsSeller"
                        switch cleaned_56
                        case 0 {
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let _122 := mload(add(mload(0x0180), 288))
                            let cleaned_59 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            cleaned_59 := and(_122, 0xffffffffffffffffffffffffffffffffffffffff)
                            /// @src 0:28109:28176  "offer.buy ? receiverIfTakerIsSeller : offer.receiverIfMakerIsSeller"
                            mstore(0x80, cleaned_59)
                        }
                        default { mstore(0x80, mload(0x0120)) }
                        /// @src 0:28254:28271  "abi.encode(offer)"
                        let expr_mpos := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                        /// @src 0:28254:28271  "abi.encode(offer)"
                        let _123 := add(expr_mpos, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32)
                        /// @src 0:28254:28271  "abi.encode(offer)"
                        let tail_7 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(_123, 32)
                        tail_7 := abi_encode_struct_Offer(mload(0x0180), add(/** @src 0:28254:28271  "abi.encode(offer)" */ expr_mpos, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 64))
                        /// @src 0:28254:28271  "abi.encode(offer)"
                        let _124 := sub(tail_7, expr_mpos)
                        mstore(expr_mpos, add(_124, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(31)))
                        /// @src 0:28254:28271  "abi.encode(offer)"
                        finalize_allocation(expr_mpos, _124)
                        /// @src 0:28244:28272  "keccak256(abi.encode(offer))"
                        let expr_34 := keccak256(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _123, mload(/** @src 0:28244:28272  "keccak256(abi.encode(offer))" */ expr_mpos))
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let _125 := mload(add(mload(0x0180), 32))
                        let cleaned_60 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        cleaned_60 := iszero(iszero(_125))
                        let _126 := mload(add(mload(0x0180), 64))
                        let cleaned_61 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        cleaned_61 := and(_126, 0xffffffffffffffffffffffffffffffffffffffff)
                        let _127 := mload(add(mload(0x0180), 192))
                        let _128 := mload(add(mload(0x0180), 320))
                        let cleaned_62 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        cleaned_62 := and(_128, 0xffffffffffffffffffffffffffffffffffffffff)
                        /// @src 0:28680:28738  "int256(buyerCreditIncrease) - int256(sellerCreditDecrease)"
                        let diff := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        diff := sub(var_z_1, var_z_2)
                        let _129 := slt(var_z_2, /** @src -1:-1:-1 */ 0)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        if or(and(iszero(_129), sgt(diff, var_z_1)), and(_129, slt(diff, var_z_1)))
                        {
                            mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(224, 0x4e487b71))
                            mstore(4, 0x11)
                            revert(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 36)
                        }
                        /// @src 0:28192:28789  "EventsLib.Take(..."
                        let _130 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                        /// @src 0:28192:28789  "EventsLib.Take(..."
                        let tail_8 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(_130, /** @src 0:23224:23234  "msg.sender" */ caller())
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(add(_130, 32), expr_34)
                        mstore(add(_130, 64), cleaned_60)
                        mstore(add(_130, 96), _127)
                        mstore(add(_130, 128), cleaned_62)
                        mstore(add(_130, 160), 0x01e0)
                        tail_8 := abi_encode_bytes(value1_2, add(_130, 0x01e0))
                        mstore(add(_130, 192), calldataload(68))
                        mstore(add(_130, 224), mload(0x0100))
                        mstore(add(_130, 256), mload(0x01a0))
                        mstore(add(_130, 288), mload(0x01e0))
                        mstore(add(_130, 320), and(mload(0xe0), 0xffffffffffffffffffffffffffffffff))
                        mstore(add(_130, 352), and(mload(0xa0), 0xffffffffffffffffffffffffffffffff))
                        mstore(add(_130, 384), diff)
                        mstore(add(_130, 416), and(mload(0x80), 0xffffffffffffffffffffffffffffffffffffffff))
                        mstore(add(_130, 448), and(expr_32, 0xffffffffffffffffffffffffffffffffffffffff))
                        /// @src 0:28192:28789  "EventsLib.Take(..."
                        log4(_130, sub(tail_8, _130), 0xbd88656d0ee14d32d4f74f814f6ccb5c750a4c542d6fdf83ee00ddca4edebff0, mload(0x0200), cleaned_61, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:23215:23234  "taker == msg.sender" */ mload(0x0220), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                        /// @src 0:28817:28876  "UtilsLib.tExchange(LIQUIDATION_LOCK_SLOT, id, seller, true)"
                        let var_previous := /** @src -1:-1:-1 */ 0
                        /// @src 12:2503:2535  "abi.encode(key1, key2, baseSlot)"
                        let expr_mpos_1 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                        /// @src 12:2503:2535  "abi.encode(key1, key2, baseSlot)"
                        let tail_9 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        tail_9 := add(/** @src 12:2503:2535  "abi.encode(key1, key2, baseSlot)" */ expr_mpos_1, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 128)
                        mstore(/** @src 12:2503:2535  "abi.encode(key1, key2, baseSlot)" */ add(expr_mpos_1, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32), mload(0x0200))
                        mstore(add(/** @src 12:2503:2535  "abi.encode(key1, key2, baseSlot)" */ expr_mpos_1, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 64), and(mload(0x01c0), 0xffffffffffffffffffffffffffffffffffffffff))
                        mstore(add(/** @src 12:2503:2535  "abi.encode(key1, key2, baseSlot)" */ expr_mpos_1, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 96), /** @src 7:945:991  "keccak256(\"morpho.midnight.liquidationLocked\")" */ 0x90e10dad8320b2f9ee6b84bebe89829c27a3fc1209e68031bc1d4b65c22e4da4)
                        /// @src 12:2503:2535  "abi.encode(key1, key2, baseSlot)"
                        mstore(expr_mpos_1, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 96)
                        /// @src 12:2503:2535  "abi.encode(key1, key2, baseSlot)"
                        finalize_allocation(expr_mpos_1, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 128)
                        /// @src 12:2493:2536  "keccak256(abi.encode(key1, key2, baseSlot))"
                        let _131 := keccak256(/** @src 12:2503:2535  "abi.encode(key1, key2, baseSlot)" */ add(expr_mpos_1, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32), mload(/** @src 12:2493:2536  "keccak256(abi.encode(key1, key2, baseSlot))" */ expr_mpos_1))
                        /// @src 12:2547:2651  "assembly (\"memory-safe\") {..."
                        var_previous := tload(_131)
                        tstore(_131, /** @src 0:23384:23395  "marketState" */ 0x01)
                        /// @src 0:28886:29306  "if (buyerCallback != address(0)) {..."
                        if /** @src 0:28002:28029  "buyerCallback != address(0)" */ iszero(iszero(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:28002:28029  "buyerCallback != address(0)" */ expr_30, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff)))
                        /// @src 0:28886:29306  "if (buyerCallback != address(0)) {..."
                        {
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let _132 := mload(add(mload(0x0180), 32))
                            let cleaned_63 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            cleaned_63 := iszero(iszero(_132))
                            /// @src 0:28966:29016  "offer.buy ? offer.callbackData : takerCallbackData"
                            let expr_mpos_2 := /** @src -1:-1:-1 */ 0
                            /// @src 0:28966:29016  "offer.buy ? offer.callbackData : takerCallbackData"
                            switch cleaned_63
                            case 0 { expr_mpos_2 := mload(0x0140) }
                            default {
                                expr_mpos_2 := /** @src 0:28978:28996  "offer.callbackData" */ mload(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ add(mload(0x0180), 256))
                            }
                            /// @src 0:29114:29126  "offer.market"
                            let _mpos := mload(mload(0x0180))
                            /// @src 0:29055:29198  "IBuyCallback(buyerCallback)..."
                            let _133 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                            /// @src 0:29055:29198  "IBuyCallback(buyerCallback)..."
                            mstore(_133, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(224, 0x1c0bb54d))
                            /// @src 0:29055:29198  "IBuyCallback(buyerCallback)..."
                            let tail_10 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            mstore(/** @src 0:29055:29198  "IBuyCallback(buyerCallback)..." */ add(_133, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 4), mload(0x0200))
                            mstore(add(/** @src 0:29055:29198  "IBuyCallback(buyerCallback)..." */ _133, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 36), 224)
                            let tail_11 := abi_encode_struct_Market(_mpos, add(/** @src 0:29055:29198  "IBuyCallback(buyerCallback)..." */ _133, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 228))
                            mstore(add(/** @src 0:29055:29198  "IBuyCallback(buyerCallback)..." */ _133, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 68), mload(0x0100))
                            mstore(add(/** @src 0:29055:29198  "IBuyCallback(buyerCallback)..." */ _133, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 100), calldataload(68))
                            mstore(add(/** @src 0:29055:29198  "IBuyCallback(buyerCallback)..." */ _133, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 132), and(mload(0xe0), 0xffffffffffffffffffffffffffffffff))
                            mstore(add(/** @src 0:29055:29198  "IBuyCallback(buyerCallback)..." */ _133, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 164), and(mload(0x0240), 0xffffffffffffffffffffffffffffffffffffffff))
                            mstore(add(/** @src 0:29055:29198  "IBuyCallback(buyerCallback)..." */ _133, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 196), add(sub(tail_11, /** @src 0:29055:29198  "IBuyCallback(buyerCallback)..." */ _133), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(3)))
                            tail_10 := abi_encode_bytes(expr_mpos_2, tail_11)
                            /// @src 0:29055:29198  "IBuyCallback(buyerCallback)..."
                            let _134 := call(gas(), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:28002:28029  "buyerCallback != address(0)" */ expr_30, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff), /** @src -1:-1:-1 */ 0, /** @src 0:29055:29198  "IBuyCallback(buyerCallback)..." */ _133, sub(tail_10, _133), _133, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32)
                            /// @src 0:29055:29198  "IBuyCallback(buyerCallback)..."
                            if iszero(_134)
                            {
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                let pos_6 := mload(64)
                                returndatacopy(pos_6, /** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ returndatasize())
                                revert(pos_6, returndatasize())
                            }
                            /// @src 0:29055:29198  "IBuyCallback(buyerCallback)..."
                            let expr_35 := /** @src -1:-1:-1 */ 0
                            /// @src 0:29055:29198  "IBuyCallback(buyerCallback)..."
                            if _134
                            {
                                let _135 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32
                                /// @src 0:29055:29198  "IBuyCallback(buyerCallback)..."
                                if gt(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32, /** @src 0:29055:29198  "IBuyCallback(buyerCallback)..." */ returndatasize()) { _135 := returndatasize() }
                                finalize_allocation(_133, _135)
                                let value0_11 := /** @src -1:-1:-1 */ 0
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                if slt(sub(/** @src 0:29055:29198  "IBuyCallback(buyerCallback)..." */ add(_133, _135), _133), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32)
                                {
                                    revert(/** @src -1:-1:-1 */ 0, 0)
                                }
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                value0_11 := mload(/** @src 0:29055:29198  "IBuyCallback(buyerCallback)..." */ _133)
                                expr_35 := value0_11
                            }
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            if iszero(/** @src 0:29055:29234  "IBuyCallback(buyerCallback)..." */ eq(expr_35, /** @src 7:1030:1074  "keccak256(\"morpho.midnight.callbackSuccess\")" */ 0x7f87788ea698181ea4d28d1576d0ba4fc92c0dbe5bf75b43692af2ce91dbaea2))
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            {
                                mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(226, 0x2a3cfad1))
                                revert(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 4)
                            }
                        }
                        /// @src 0:29349:29371  "offer.market.loanToken"
                        let _136 := add(/** @src 0:29349:29361  "offer.market" */ mload(mload(0x0180)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 64)
                        /// @src 0:29349:29371  "offer.market.loanToken"
                        let returnValue_1 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        returnValue_1 := and(mload(_136), 0xffffffffffffffffffffffffffffffffffffffff)
                        /// @src 0:29395:29421  "buyerAssets - sellerAssets"
                        fun_safeTransferFrom(returnValue_1, expr_32, /** @src 0:29388:29392  "this" */ address(), /** @src 0:29395:29421  "buyerAssets - sellerAssets" */ checked_sub_uint256(mload(0x0100), mload(0x01a0)))
                        /// @src 0:29465:29487  "offer.market.loanToken"
                        let _137 := add(/** @src 0:29465:29477  "offer.market" */ mload(mload(0x0180)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 64)
                        /// @src 0:29465:29487  "offer.market.loanToken"
                        let returnValue_2 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        returnValue_2 := and(mload(_137), 0xffffffffffffffffffffffffffffffffffffffff)
                        /// @src 0:29506:29518  "sellerAssets"
                        fun_safeTransferFrom(/** @src 0:29465:29487  "offer.market.loanToken" */ returnValue_2, /** @src 0:29506:29518  "sellerAssets" */ expr_32, mload(0x80), mload(0x01a0))
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let _138 := and(/** @src 0:29534:29562  "sellerCallback != address(0)" */ expr_31, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff)
                        /// @src 0:29530:30168  "if (sellerCallback != address(0)) {..."
                        if /** @src 0:29534:29562  "sellerCallback != address(0)" */ iszero(iszero(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _138))
                        /// @src 0:29530:30168  "if (sellerCallback != address(0)) {..."
                        {
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let _139 := mload(add(mload(0x0180), 32))
                            let cleaned_64 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            cleaned_64 := iszero(iszero(_139))
                            /// @src 0:29612:29662  "offer.buy ? takerCallbackData : offer.callbackData"
                            let expr_mpos_3 := /** @src -1:-1:-1 */ 0
                            /// @src 0:29612:29662  "offer.buy ? takerCallbackData : offer.callbackData"
                            switch cleaned_64
                            case 0 {
                                expr_mpos_3 := /** @src 0:29644:29662  "offer.callbackData" */ mload(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ add(mload(0x0180), 256))
                            }
                            default /// @src 0:29612:29662  "offer.buy ? takerCallbackData : offer.callbackData"
                            { expr_mpos_3 := mload(0x0140) }
                            /// @src 0:29812:29824  "offer.market"
                            let _mpos_1 := mload(mload(0x0180))
                            /// @src 0:29701:30075  "ISellCallback(sellerCallback)..."
                            let _140 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                            /// @src 0:29701:30075  "ISellCallback(sellerCallback)..."
                            mstore(_140, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(225, 0x36790c21))
                            /// @src 0:29701:30075  "ISellCallback(sellerCallback)..."
                            let tail_12 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            mstore(/** @src 0:29701:30075  "ISellCallback(sellerCallback)..." */ add(_140, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 4), mload(0x0200))
                            mstore(add(/** @src 0:29701:30075  "ISellCallback(sellerCallback)..." */ _140, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 36), 256)
                            let tail_13 := abi_encode_struct_Market(_mpos_1, add(/** @src 0:29701:30075  "ISellCallback(sellerCallback)..." */ _140, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 260))
                            mstore(add(/** @src 0:29701:30075  "ISellCallback(sellerCallback)..." */ _140, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 68), mload(0x01a0))
                            mstore(add(/** @src 0:29701:30075  "ISellCallback(sellerCallback)..." */ _140, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 100), calldataload(68))
                            mstore(add(/** @src 0:29701:30075  "ISellCallback(sellerCallback)..." */ _140, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 132), and(mload(0xa0), 0xffffffffffffffffffffffffffffffff))
                            mstore(add(/** @src 0:29701:30075  "ISellCallback(sellerCallback)..." */ _140, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 164), and(mload(0x01c0), 0xffffffffffffffffffffffffffffffffffffffff))
                            mstore(add(/** @src 0:29701:30075  "ISellCallback(sellerCallback)..." */ _140, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 196), and(mload(0x80), 0xffffffffffffffffffffffffffffffffffffffff))
                            mstore(add(/** @src 0:29701:30075  "ISellCallback(sellerCallback)..." */ _140, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 228), add(sub(tail_13, /** @src 0:29701:30075  "ISellCallback(sellerCallback)..." */ _140), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(3)))
                            tail_12 := abi_encode_bytes(expr_mpos_3, tail_13)
                            /// @src 0:29701:30075  "ISellCallback(sellerCallback)..."
                            let _141 := call(gas(), _138, /** @src -1:-1:-1 */ 0, /** @src 0:29701:30075  "ISellCallback(sellerCallback)..." */ _140, sub(tail_12, _140), _140, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32)
                            /// @src 0:29701:30075  "ISellCallback(sellerCallback)..."
                            if iszero(_141)
                            {
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                let pos_7 := mload(64)
                                returndatacopy(pos_7, /** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ returndatasize())
                                revert(pos_7, returndatasize())
                            }
                            /// @src 0:29701:30075  "ISellCallback(sellerCallback)..."
                            let expr_36 := /** @src -1:-1:-1 */ 0
                            /// @src 0:29701:30075  "ISellCallback(sellerCallback)..."
                            if _141
                            {
                                let _142 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32
                                /// @src 0:29701:30075  "ISellCallback(sellerCallback)..."
                                if gt(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32, /** @src 0:29701:30075  "ISellCallback(sellerCallback)..." */ returndatasize()) { _142 := returndatasize() }
                                finalize_allocation(_140, _142)
                                let value0_12 := /** @src -1:-1:-1 */ 0
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                if slt(sub(/** @src 0:29701:30075  "ISellCallback(sellerCallback)..." */ add(_140, _142), _140), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32)
                                {
                                    revert(/** @src -1:-1:-1 */ 0, 0)
                                }
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                value0_12 := mload(/** @src 0:29701:30075  "ISellCallback(sellerCallback)..." */ _140)
                                expr_36 := value0_12
                            }
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            if iszero(/** @src 0:29701:30095  "ISellCallback(sellerCallback)..." */ eq(expr_36, /** @src 7:1030:1074  "keccak256(\"morpho.midnight.callbackSuccess\")" */ 0x7f87788ea698181ea4d28d1576d0ba4fc92c0dbe5bf75b43692af2ce91dbaea2))
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            {
                                mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(224, 0xa4fb7883))
                                revert(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 4)
                            }
                        }
                        /// @src 0:30177:30253  "if (!wasLocked) UtilsLib.tExchange(LIQUIDATION_LOCK_SLOT, id, seller, false)"
                        if /** @src 0:30181:30191  "!wasLocked" */ iszero(var_previous)
                        /// @src 0:30177:30253  "if (!wasLocked) UtilsLib.tExchange(LIQUIDATION_LOCK_SLOT, id, seller, false)"
                        {
                            /// @src 0:30193:30253  "UtilsLib.tExchange(LIQUIDATION_LOCK_SLOT, id, seller, false)"
                            pop(fun_tExchange(mload(0x0200), mload(0x01c0)))
                        }
                        /// @src 0:30271:30339  "liquidationLocked(id, seller) || isHealthy(offer.market, id, seller)"
                        let expr_37 := /** @src 0:54472:54518  "UtilsLib.tGet(LIQUIDATION_LOCK_SLOT, id, user)" */ fun_tGet(/** @src 0:30271:30300  "liquidationLocked(id, seller)" */ mload(0x0200), mload(0x01c0))
                        /// @src 0:30271:30339  "liquidationLocked(id, seller) || isHealthy(offer.market, id, seller)"
                        if iszero(expr_37)
                        {
                            expr_37 := /** @src 0:30304:30339  "isHealthy(offer.market, id, seller)" */ fun_isHealthy(/** @src 0:30314:30326  "offer.market" */ mload(mload(0x0180)), /** @src 0:30304:30339  "isHealthy(offer.market, id, seller)" */ mload(0x0200), mload(0x01c0))
                        }
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        if iszero(expr_37)
                        {
                            mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(224, 0x4aa98809))
                            revert(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 4)
                        }
                        let memPos_10 := mload(64)
                        mstore(memPos_10, mload(0x0100))
                        mstore(add(memPos_10, 32), mload(0x01a0))
                        return(memPos_10, 64)
                    }
                    case 0x6b210f9e {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), 160)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let offset_10 := calldataload(4)
                        if gt(offset_10, 0xffffffffffffffff)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let value0_13 := abi_decode_struct_Market(add(4, offset_10), calldatasize())
                        let value_25 := calldataload(36)
                        let value2_3 := abi_decode_address_44128()
                        let value3_1 := abi_decode_address_44129()
                        let offset_11 := calldataload(132)
                        if gt(offset_11, 0xffffffffffffffff)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let value4_1, value5_1 := abi_decode_bytes_calldata(add(4, offset_11), calldatasize())
                        let _143 := and(/** @src 0:31588:31610  "onBehalf == msg.sender" */ value2_3, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff)
                        /// @src 0:31588:31648  "onBehalf == msg.sender || isAuthorized[onBehalf][msg.sender]"
                        let expr_38 := /** @src 0:31588:31610  "onBehalf == msg.sender" */ eq(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _143, /** @src 0:31600:31610  "msg.sender" */ caller())
                        /// @src 0:31588:31648  "onBehalf == msg.sender || isAuthorized[onBehalf][msg.sender]"
                        if iszero(expr_38)
                        {
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            mstore(mload(0x0320), _143)
                            mstore(32, /** @src 0:31614:31626  "isAuthorized" */ 0x03)
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let dataSlot_22 := keccak256(mload(0x0320), 64)
                            /// @src 0:31614:31648  "isAuthorized[onBehalf][msg.sender]"
                            let dataSlot_23 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:31600:31610  "msg.sender" */ caller(), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                            mstore(0x20, /** @src 0:31614:31636  "isAuthorized[onBehalf]" */ dataSlot_22)
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            dataSlot_23 := keccak256(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x40)
                            /// @src 0:31588:31648  "onBehalf == msg.sender || isAuthorized[onBehalf][msg.sender]"
                            expr_38 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(sload(/** @src 0:31614:31648  "isAuthorized[onBehalf][msg.sender]" */ dataSlot_23), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xff)
                        }
                        if iszero(expr_38)
                        {
                            mstore(mload(0x0320), shl(232, 8565801))
                            revert(mload(0x0320), 4)
                        }
                        /// @src 0:31688:31707  "touchMarket(market)"
                        let expr_39 := fun_touchMarket(value0_13)
                        /// @src 0:31749:31774  "UtilsLib.toUint128(units)"
                        let expr_40 := fun_toUint128(value_25)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(mload(0x0320), expr_39)
                        mstore(32, mload(0x0320))
                        let dataSlot_24 := keccak256(mload(0x0320), 64)
                        /// @src 0:31718:31740  "position[id][onBehalf]"
                        let dataSlot_25 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _143)
                        mstore(0x20, /** @src 0:31718:31730  "position[id]" */ dataSlot_24)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        dataSlot_25 := keccak256(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x40)
                        /// @src 0:31718:31745  "position[id][onBehalf].debt"
                        let _144 := add(/** @src 0:31718:31740  "position[id][onBehalf]" */ dataSlot_25, /** @src 0:31718:31745  "position[id][onBehalf].debt" */ 2)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        sstore(/** @src 0:31718:31774  "position[id][onBehalf].debt -= UtilsLib.toUint128(units)" */ _144, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ or(and(sload(/** @src 0:31718:31774  "position[id][onBehalf].debt -= UtilsLib.toUint128(units)" */ _144), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(0xffffffffffffffffffffffffffffffff)), and(/** @src 0:31718:31774  "position[id][onBehalf].debt -= UtilsLib.toUint128(units)" */ checked_sub_uint128(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(sload(/** @src 0:31718:31774  "position[id][onBehalf].debt -= UtilsLib.toUint128(units)" */ _144), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff), /** @src 0:31718:31774  "position[id][onBehalf].debt -= UtilsLib.toUint128(units)" */ expr_40), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)))
                        /// @src 0:31816:31841  "UtilsLib.toUint128(units)"
                        let expr_41 := fun_toUint128(value_25)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(mload(0x0320), expr_39)
                        mstore(32, 1)
                        /// @src 0:31784:31812  "marketState[id].withdrawable"
                        let _145 := add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ keccak256(mload(0x0320), 64), 1)
                        sstore(/** @src 0:31784:31841  "marketState[id].withdrawable += UtilsLib.toUint128(units)" */ _145, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ or(and(sload(/** @src 0:31784:31841  "marketState[id].withdrawable += UtilsLib.toUint128(units)" */ _145), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(0xffffffffffffffffffffffffffffffff)), and(/** @src 0:31784:31841  "marketState[id].withdrawable += UtilsLib.toUint128(units)" */ checked_add_uint128(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(sload(/** @src 0:31784:31841  "marketState[id].withdrawable += UtilsLib.toUint128(units)" */ _145), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff), /** @src 0:31784:31841  "marketState[id].withdrawable += UtilsLib.toUint128(units)" */ expr_41), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)))
                        let _146 := and(/** @src 0:31868:31890  "callback != address(0)" */ value3_1, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff)
                        /// @src 0:31868:31890  "callback != address(0)"
                        let expr_42 := iszero(iszero(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _146))
                        /// @src 0:31868:31914  "callback != address(0) ? callback : msg.sender"
                        let expr_43 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x0320)
                        /// @src 0:31868:31914  "callback != address(0) ? callback : msg.sender"
                        switch expr_42
                        case 0 {
                            expr_43 := /** @src 0:31600:31610  "msg.sender" */ caller()
                        }
                        default /// @src 0:31868:31914  "callback != address(0) ? callback : msg.sender"
                        { expr_43 := value3_1 }
                        /// @src 0:31929:31984  "EventsLib.Repay(msg.sender, id, units, onBehalf, payer)"
                        let _147 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                        mstore(_147, value_25)
                        mstore(add(_147, 32), and(expr_43, 0xffffffffffffffffffffffffffffffffffffffff))
                        /// @src 0:31929:31984  "EventsLib.Repay(msg.sender, id, units, onBehalf, payer)"
                        log4(_147, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 64, /** @src 0:31929:31984  "EventsLib.Repay(msg.sender, id, units, onBehalf, payer)" */ 0x8b2d9c5b5a1393c4a278da77a782a77bfd7ef753c26429830b006487d3167088, /** @src 0:31600:31610  "msg.sender" */ caller(), /** @src 0:31929:31984  "EventsLib.Repay(msg.sender, id, units, onBehalf, payer)" */ expr_39, _143)
                        /// @src 0:31995:32223  "if (callback != address(0)) {..."
                        if expr_42
                        {
                            /// @src 0:32062:32129  "IRepayCallback(callback).onRepay(id, market, units, onBehalf, data)"
                            let _148 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                            /// @src 0:32062:32129  "IRepayCallback(callback).onRepay(id, market, units, onBehalf, data)"
                            mstore(_148, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(226, 0x0a43bd29))
                            mstore(/** @src 0:32062:32129  "IRepayCallback(callback).onRepay(id, market, units, onBehalf, data)" */ add(_148, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 4), expr_39)
                            mstore(add(/** @src 0:32062:32129  "IRepayCallback(callback).onRepay(id, market, units, onBehalf, data)" */ _148, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 36), 160)
                            let tail_14 := abi_encode_struct_Market(value0_13, add(/** @src 0:32062:32129  "IRepayCallback(callback).onRepay(id, market, units, onBehalf, data)" */ _148, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 164))
                            mstore(add(/** @src 0:32062:32129  "IRepayCallback(callback).onRepay(id, market, units, onBehalf, data)" */ _148, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 68), value_25)
                            mstore(add(/** @src 0:32062:32129  "IRepayCallback(callback).onRepay(id, market, units, onBehalf, data)" */ _148, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 100), _143)
                            mstore(add(/** @src 0:32062:32129  "IRepayCallback(callback).onRepay(id, market, units, onBehalf, data)" */ _148, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 132), add(sub(tail_14, /** @src 0:32062:32129  "IRepayCallback(callback).onRepay(id, market, units, onBehalf, data)" */ _148), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(3)))
                            /// @src 0:32062:32129  "IRepayCallback(callback).onRepay(id, market, units, onBehalf, data)"
                            let _149 := call(gas(), _146, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x0320), /** @src 0:32062:32129  "IRepayCallback(callback).onRepay(id, market, units, onBehalf, data)" */ _148, sub(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ abi_encode_bytes_calldata(value4_1, value5_1, tail_14), /** @src 0:32062:32129  "IRepayCallback(callback).onRepay(id, market, units, onBehalf, data)" */ _148), _148, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32)
                            /// @src 0:32062:32129  "IRepayCallback(callback).onRepay(id, market, units, onBehalf, data)"
                            if iszero(_149)
                            {
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                let pos_8 := mload(64)
                                returndatacopy(pos_8, mload(0x0320), returndatasize())
                                revert(pos_8, returndatasize())
                            }
                            /// @src 0:32062:32129  "IRepayCallback(callback).onRepay(id, market, units, onBehalf, data)"
                            let expr_44 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x0320)
                            /// @src 0:32062:32129  "IRepayCallback(callback).onRepay(id, market, units, onBehalf, data)"
                            if _149
                            {
                                let _150 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32
                                /// @src 0:32062:32129  "IRepayCallback(callback).onRepay(id, market, units, onBehalf, data)"
                                if gt(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32, /** @src 0:32062:32129  "IRepayCallback(callback).onRepay(id, market, units, onBehalf, data)" */ returndatasize()) { _150 := returndatasize() }
                                finalize_allocation(_148, _150)
                                let value0_14 := /** @src -1:-1:-1 */ 0
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                if slt(sub(/** @src 0:32062:32129  "IRepayCallback(callback).onRepay(id, market, units, onBehalf, data)" */ add(_148, _150), _148), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32)
                                {
                                    revert(/** @src -1:-1:-1 */ 0, 0)
                                }
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                value0_14 := mload(/** @src 0:32062:32129  "IRepayCallback(callback).onRepay(id, market, units, onBehalf, data)" */ _148)
                                expr_44 := value0_14
                            }
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            if iszero(/** @src 0:32062:32149  "IRepayCallback(callback).onRepay(id, market, units, onBehalf, data) == CALLBACK_SUCCESS" */ eq(expr_44, /** @src 7:1030:1074  "keccak256(\"morpho.midnight.callbackSuccess\")" */ 0x7f87788ea698181ea4d28d1576d0ba4fc92c0dbe5bf75b43692af2ce91dbaea2))
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            {
                                mstore(mload(0x0320), shl(225, 0x20509ed1))
                                revert(mload(0x0320), 4)
                            }
                        }
                        let cleaned_65 := and(mload(/** @src 0:32265:32281  "market.loanToken" */ add(value0_13, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 64)), 0xffffffffffffffffffffffffffffffffffffffff)
                        /// @src 0:32305:32310  "units"
                        fun_safeTransferFrom(cleaned_65, expr_43, /** @src 0:32298:32302  "this" */ address(), /** @src 0:32305:32310  "units" */ value_25)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        return(mload(0x0320), mload(0x0320))
                    }
                    case 0x7cf43d8c {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), 32)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        mstore(mload(0x0320), calldataload(4))
                        mstore(32, 1)
                        let cleaned_66 := and(sload(/** @src 0:53296:53324  "marketState[id].withdrawable" */ add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ keccak256(mload(0x0320), 64), 1)), 0xffffffffffffffffffffffffffffffff)
                        let memPos_11 := mload(64)
                        mstore(memPos_11, cleaned_66)
                        return(memPos_11, 32)
                    }
                    case 0x81cbd3ea {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), mload(0x0320))
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let value_26 := and(sload(/** @src 0:14783:14808  "address public feeClaimer" */ 11), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff)
                        let memPos_12 := mload(64)
                        mstore(memPos_12, value_26)
                        return(memPos_12, 32)
                    }
                    case 0x87cf3ef4 {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), mload(0x0320))
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let value_27 := and(sload(/** @src 0:14753:14777  "address public feeSetter" */ 10), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff)
                        let memPos_13 := mload(64)
                        mstore(memPos_13, value_27)
                        return(memPos_13, 32)
                    }
                    case 0x8c366a0a {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), 64)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let value1_3 := abi_decode_address_44120()
                        mstore(mload(0x0320), calldataload(4))
                        mstore(32, mload(0x0320))
                        let dataSlot_26 := keccak256(mload(0x0320), 64)
                        /// @src 0:52355:52373  "position[id][user]"
                        let dataSlot_27 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:52355:52373  "position[id][user]" */ value1_3, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                        mstore(0x20, /** @src 0:52355:52367  "position[id]" */ dataSlot_26)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        dataSlot_27 := keccak256(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x40)
                        let cleaned_67 := and(sload(/** @src 0:52355:52388  "position[id][user].lastLossFactor" */ add(/** @src 0:52355:52373  "position[id][user]" */ dataSlot_27, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 1)), 0xffffffffffffffffffffffffffffffff)
                        let memPos_14 := mload(64)
                        mstore(memPos_14, cleaned_67)
                        return(memPos_14, 32)
                    }
                    case 0x8d2ba1d6 {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), 32)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        mstore(mload(0x0320), calldataload(4))
                        mstore(32, /** @src 0:14638:14714  "mapping(uint256 liquidationCursor => bool) public isLiquidationCursorEnabled" */ 8)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let value_28 := and(sload(keccak256(mload(0x0320), 64)), 0xff)
                        let memPos_15 := mload(64)
                        mstore(memPos_15, iszero(iszero(value_28)))
                        return(memPos_15, 32)
                    }
                    case 0x8fd76a21 {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), 32)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let value_29 := calldataload(4)
                        if iszero(/** @src 0:17145:17171  "msg.sender == configurator" */ eq(/** @src 0:17145:17155  "msg.sender" */ caller(), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(sload(/** @src 0:17159:17171  "configurator" */ 0x09), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff)))
                        {
                            mstore(mload(0x0320), shl(228, 0x033b71e1))
                            revert(mload(0x0320), 4)
                        }
                        if iszero(/** @src 0:17210:17233  "liquidationCursor < WAD" */ lt(value_29, /** @src 7:190:194  "1e18" */ 0x0de0b6b3a7640000))
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        {
                            mstore(mload(0x0320), shl(229, 0x05960a25))
                            revert(mload(0x0320), 4)
                        }
                        mstore(mload(0x0320), value_29)
                        mstore(32, /** @src 0:17272:17298  "isLiquidationCursorEnabled" */ 0x08)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let dataSlot_28 := keccak256(mload(0x0320), 64)
                        /// @src 7:190:194  "1e18"
                        sstore(dataSlot_28, or(and(sload(dataSlot_28), not(255)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 1))
                        /// @src 0:17339:17391  "EventsLib.EnableLiquidationCursor(liquidationCursor)"
                        let _151 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                        mstore(_151, value_29)
                        /// @src 0:17339:17391  "EventsLib.EnableLiquidationCursor(liquidationCursor)"
                        log1(_151, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32, /** @src 0:17339:17391  "EventsLib.EnableLiquidationCursor(liquidationCursor)" */ 0xafc3bc0c69f51b1b5ebb2d1dcb58f842f71728ad18fe029e19ac37b9d981a50e)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        return(mload(0x0320), mload(0x0320))
                    }
                    case 0x93af51c2 {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), 64)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let value1_4 := abi_decode_address_44120()
                        mstore(mload(0x0320), calldataload(4))
                        mstore(32, mload(0x0320))
                        let dataSlot_29 := keccak256(mload(0x0320), 64)
                        /// @src 0:52629:52647  "position[id][user]"
                        let dataSlot_30 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:52629:52647  "position[id][user]" */ value1_4, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                        mstore(0x20, /** @src 0:52629:52641  "position[id]" */ dataSlot_29)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        dataSlot_30 := keccak256(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x40)
                        let cleaned_68 := and(sload(/** @src 0:52629:52652  "position[id][user].debt" */ add(/** @src 0:52629:52647  "position[id][user]" */ dataSlot_30, /** @src 0:52629:52652  "position[id][user].debt" */ 2)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)
                        let memPos_16 := mload(64)
                        mstore(memPos_16, cleaned_68)
                        return(memPos_16, 32)
                    }
                    case 0x93c52062 {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), 64)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let value1_5 := abi_decode_address_44120()
                        mstore(mload(0x0320), calldataload(4))
                        mstore(32, mload(0x0320))
                        let dataSlot_31 := keccak256(mload(0x0320), 64)
                        /// @src 0:14058:14130  "mapping(bytes32 id => mapping(address user => Position)) public position"
                        let dataSlot_32 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:14058:14130  "mapping(bytes32 id => mapping(address user => Position)) public position" */ value1_5, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                        mstore(0x20, /** @src 0:14058:14130  "mapping(bytes32 id => mapping(address user => Position)) public position" */ dataSlot_31)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        dataSlot_32 := keccak256(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x40)
                        let _152 := sload(/** @src 0:14058:14130  "mapping(bytes32 id => mapping(address user => Position)) public position" */ dataSlot_32)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let _153 := sload(/** @src 0:14058:14130  "mapping(bytes32 id => mapping(address user => Position)) public position" */ add(dataSlot_32, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 1))
                        let _154 := sload(/** @src 0:14058:14130  "mapping(bytes32 id => mapping(address user => Position)) public position" */ add(dataSlot_32, 2))
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let memPos_17 := mload(64)
                        mstore(memPos_17, and(_152, 0xffffffffffffffffffffffffffffffff))
                        mstore(add(memPos_17, 32), shr(128, _152))
                        mstore(add(memPos_17, 64), and(_153, 0xffffffffffffffffffffffffffffffff))
                        mstore(add(memPos_17, 96), shr(128, _153))
                        mstore(add(memPos_17, 128), and(_154, 0xffffffffffffffffffffffffffffffff))
                        mstore(add(memPos_17, 160), shr(128, _154))
                        return(memPos_17, 192)
                    }
                    case 0x98285e82 {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), mload(0x0320))
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let value_30 := and(sload(/** @src 0:14814:14846  "address public tickSpacingSetter" */ 12), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff)
                        let memPos_18 := mload(64)
                        mstore(memPos_18, value_30)
                        return(memPos_18, 32)
                    }
                    case 0x9e3ff40a {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), 96)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let value_31 := calldataload(4)
                        let value_32 := calldataload(36)
                        let value_33 := calldataload(68)
                        mstore(mload(0x0320), value_31)
                        mstore(32, 1)
                        let dataSlot_33 := keccak256(mload(0x0320), 64)
                        if iszero(/** @src 0:18264:18287  "msg.sender == feeSetter" */ eq(/** @src 0:18264:18274  "msg.sender" */ caller(), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(sload(/** @src 0:18278:18287  "feeSetter" */ 0x0a), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff)))
                        {
                            mstore(mload(0x0320), shl(224, 0x7155bb19))
                            revert(mload(0x0320), 4)
                        }
                        if /** @src 0:18323:18333  "index <= 6" */ gt(value_32, /** @src 0:18332:18333  "6" */ 0x06)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        {
                            mstore(mload(0x0320), shl(224, 0x37f6201f))
                            revert(mload(0x0320), 4)
                        }
                        if /** @src 0:18371:18414  "newSettlementFee <= maxSettlementFee(index)" */ gt(value_33, /** @src 0:18391:18414  "maxSettlementFee(index)" */ fun_maxSettlementFee(value_32))
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        {
                            mstore(mload(0x0320), shl(226, 0x3faa18af))
                            revert(mload(0x0320), 4)
                        }
                        /// @src 7:263:267  "1e12"
                        if iszero(/** @src 0:18458:18485  "newSettlementFee % CBP == 0" */ iszero(/** @src 7:263:267  "1e12" */ mod(value_33, 0xe8d4a51000)))
                        {
                            mstore(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x0320), /** @src 7:263:267  "1e12" */ shl(224, 0x1468c5cb))
                            revert(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x0320), 4)
                        }
                        /// @src 0:18530:18554  "_marketState.tickSpacing"
                        let _155 := add(dataSlot_33, 2)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        if /** @src 0:18530:18558  "_marketState.tickSpacing > 0" */ iszero(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(shr(144, sload(/** @src 0:18530:18554  "_marketState.tickSpacing" */ _155)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xff))
                        {
                            mstore(mload(0x0320), shl(224, 0x96e13529))
                            revert(mload(0x0320), 4)
                        }
                        let cleaned_69 := and(div(value_33, /** @src 7:263:267  "1e12" */ 0xe8d4a51000), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffff)
                        /// @src 0:18776:19342  "if (index == 0) _marketState.settlementFeeCbp0 = newSettlementFeeCbp;..."
                        switch /** @src 0:18780:18790  "index == 0" */ iszero(value_32)
                        case /** @src 0:18776:19342  "if (index == 0) _marketState.settlementFeeCbp0 = newSettlementFeeCbp;..." */ 0 {
                            /// @src 0:18859:19342  "if (index == 1) _marketState.settlementFeeCbp1 = newSettlementFeeCbp;..."
                            switch /** @src 0:18863:18873  "index == 1" */ eq(value_32, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 1)
                            case /** @src 0:18859:19342  "if (index == 1) _marketState.settlementFeeCbp1 = newSettlementFeeCbp;..." */ 0 {
                                /// @src 0:18942:19342  "if (index == 2) _marketState.settlementFeeCbp2 = newSettlementFeeCbp;..."
                                switch /** @src 0:18946:18956  "index == 2" */ eq(value_32, /** @src 0:18530:18554  "_marketState.tickSpacing" */ 2)
                                case /** @src 0:18942:19342  "if (index == 2) _marketState.settlementFeeCbp2 = newSettlementFeeCbp;..." */ 0 {
                                    /// @src 0:19025:19342  "if (index == 3) _marketState.settlementFeeCbp3 = newSettlementFeeCbp;..."
                                    switch /** @src 0:19029:19039  "index == 3" */ eq(value_32, /** @src 0:19038:19039  "3" */ 0x03)
                                    case /** @src 0:19025:19342  "if (index == 3) _marketState.settlementFeeCbp3 = newSettlementFeeCbp;..." */ 0 {
                                        /// @src 0:19108:19342  "if (index == 4) _marketState.settlementFeeCbp4 = newSettlementFeeCbp;..."
                                        switch /** @src 0:19112:19122  "index == 4" */ eq(value_32, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 4)
                                        case /** @src 0:19108:19342  "if (index == 4) _marketState.settlementFeeCbp4 = newSettlementFeeCbp;..." */ 0 {
                                            /// @src 0:19191:19342  "if (index == 5) _marketState.settlementFeeCbp5 = newSettlementFeeCbp;..."
                                            switch /** @src 0:19195:19205  "index == 5" */ eq(value_32, /** @src 0:19204:19205  "5" */ 0x05)
                                            case /** @src 0:19191:19342  "if (index == 5) _marketState.settlementFeeCbp5 = newSettlementFeeCbp;..." */ 0 {
                                                /// @src 0:19274:19342  "if (index == 6) _marketState.settlementFeeCbp6 = newSettlementFeeCbp"
                                                if /** @src 0:19278:19288  "index == 6" */ eq(value_32, /** @src 0:18332:18333  "6" */ 0x06)
                                                /// @src 0:19274:19342  "if (index == 6) _marketState.settlementFeeCbp6 = newSettlementFeeCbp"
                                                {
                                                    /// @src 0:19290:19342  "_marketState.settlementFeeCbp6 = newSettlementFeeCbp"
                                                    update_storage_value_offset_12_uint16_to_uint16(_155, cleaned_69)
                                                }
                                            }
                                            default /// @src 0:19191:19342  "if (index == 5) _marketState.settlementFeeCbp5 = newSettlementFeeCbp;..."
                                            {
                                                /// @src 0:19207:19259  "_marketState.settlementFeeCbp5 = newSettlementFeeCbp"
                                                update_storage_value_offset_uint16_to_uint16(_155, cleaned_69)
                                            }
                                        }
                                        default /// @src 0:19108:19342  "if (index == 4) _marketState.settlementFeeCbp4 = newSettlementFeeCbp;..."
                                        {
                                            /// @src 0:19124:19176  "_marketState.settlementFeeCbp4 = newSettlementFeeCbp"
                                            update_storage_value_offset_8_uint16_to_uint16(_155, cleaned_69)
                                        }
                                    }
                                    default /// @src 0:19025:19342  "if (index == 3) _marketState.settlementFeeCbp3 = newSettlementFeeCbp;..."
                                    {
                                        /// @src 0:19041:19093  "_marketState.settlementFeeCbp3 = newSettlementFeeCbp"
                                        update_storage_value_offset_t_uint16_to_t_uint16(_155, cleaned_69)
                                    }
                                }
                                default /// @src 0:18942:19342  "if (index == 2) _marketState.settlementFeeCbp2 = newSettlementFeeCbp;..."
                                {
                                    /// @src 0:18958:19010  "_marketState.settlementFeeCbp2 = newSettlementFeeCbp"
                                    update_storage_value_offset_4_uint16_to_uint16(_155, cleaned_69)
                                }
                            }
                            default /// @src 0:18859:19342  "if (index == 1) _marketState.settlementFeeCbp1 = newSettlementFeeCbp;..."
                            {
                                /// @src 0:18875:18927  "_marketState.settlementFeeCbp1 = newSettlementFeeCbp"
                                update_storage_value_offset_2_uint16_to_uint16(_155, cleaned_69)
                            }
                        }
                        default /// @src 0:18776:19342  "if (index == 0) _marketState.settlementFeeCbp0 = newSettlementFeeCbp;..."
                        {
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            sstore(/** @src 0:18792:18844  "_marketState.settlementFeeCbp0 = newSettlementFeeCbp" */ _155, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ or(and(sload(/** @src 0:18792:18844  "_marketState.settlementFeeCbp0 = newSettlementFeeCbp" */ _155), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(65535)), and(/** @src 0:18792:18844  "_marketState.settlementFeeCbp0 = newSettlementFeeCbp" */ cleaned_69, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffff)))
                        }
                        /// @src 0:19357:19418  "EventsLib.SetMarketSettlementFee(id, index, newSettlementFee)"
                        let _156 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                        mstore(_156, value_33)
                        /// @src 0:19357:19418  "EventsLib.SetMarketSettlementFee(id, index, newSettlementFee)"
                        log3(_156, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32, /** @src 0:19357:19418  "EventsLib.SetMarketSettlementFee(id, index, newSettlementFee)" */ 0xd316faedf187698c4bd62cf9b5484dd13466d6504d0d98ff5eb0110b2d325e17, value_31, value_32)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        return(mload(0x0320), mload(0x0320))
                    }
                    case 0x9e580092 {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), 288)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if gt(calldataload(4), 0xffffffffffffffff)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(sub(calldatasize(), calldataload(4)), not(3)), 256)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let value4_2 := abi_decode_address_44141()
                        let value_34 := /** @src -1:-1:-1 */ mload(0x0320)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        value_34 := calldataload(164)
                        if iszero(eq(value_34, iszero(iszero(value_34))))
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let value_35 := /** @src -1:-1:-1 */ mload(0x0320)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        value_35 := calldataload(196)
                        if iszero(eq(value_35, and(value_35, 0xffffffffffffffffffffffffffffffffffffffff)))
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        mstore(0x02e0, /** @src -1:-1:-1 */ mload(0x0320))
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(0x02e0, calldataload(228))
                        if iszero(eq(mload(0x02e0), and(mload(0x02e0), 0xffffffffffffffffffffffffffffffffffffffff)))
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let offset_12 := calldataload(260)
                        if gt(offset_12, 0xffffffffffffffff)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let value8, value9 := abi_decode_bytes_calldata(add(4, offset_12), calldatasize())
                        mstore(0x0260, calldataload(100))
                        mstore(0x0280, calldataload(68))
                        /// @src 0:35638:35657  "touchMarket(market)"
                        mstore(0x0300, fun_touchMarket(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ abi_decode_struct_Market(add(4, calldataload(4)), calldatasize())))
                        mstore(mload(0x0320), mload(0x0300))
                        mstore(32, 1)
                        mstore(0x02a0, keccak256(mload(0x0320), 64))
                        mstore(mload(0x0320), mload(0x0300))
                        mstore(32, mload(0x0320))
                        let dataSlot_34 := keccak256(mload(0x0320), 64)
                        /// @src 0:35756:35778  "position[id][borrower]"
                        let dataSlot_35 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:35756:35778  "position[id][borrower]" */ value4_2, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                        mstore(0x20, /** @src 0:35756:35768  "position[id]" */ dataSlot_34)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        dataSlot_35 := keccak256(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x40)
                        /// @src 0:35796:35833  "repaidUnits == 0 || seizedAssets == 0"
                        let expr_45 := /** @src 0:35796:35812  "repaidUnits == 0" */ iszero(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(100))
                        /// @src 0:35796:35812  "repaidUnits == 0"
                        let expr_46 := /** @src 0:35796:35833  "repaidUnits == 0 || seizedAssets == 0" */ expr_45
                        let _157 := iszero(expr_45)
                        if _157
                        {
                            expr_45 := /** @src 0:35816:35833  "seizedAssets == 0" */ iszero(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(68))
                        }
                        if iszero(expr_45)
                        {
                            mstore(mload(0x0320), shl(224, 0xf0732dd7))
                            revert(mload(0x0320), 4)
                        }
                        let _158 := sload(/** @src 0:35873:35887  "_position.debt" */ add(/** @src 0:35756:35778  "position[id][borrower]" */ dataSlot_35, /** @src 0:35873:35887  "_position.debt" */ 2))
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        if /** @src 0:35873:35891  "_position.debt > 0" */ iszero(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(_158, 0xffffffffffffffffffffffffffffffff))
                        {
                            mstore(mload(0x0320), shl(227, 0x1963d1e7))
                            revert(mload(0x0320), 4)
                        }
                        /// @src 0:35996:36098  "market.liquidatorGate == address(0) || ILiquidatorGate(market.liquidatorGate).canLiquidate(msg.sender)"
                        let expr_47 := /** @src 0:35996:36031  "market.liquidatorGate == address(0)" */ iszero(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:35996:36017  "market.liquidatorGate" */ read_from_calldatat_address(add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(4), 228)), 0xffffffffffffffffffffffffffffffffffffffff))
                        /// @src 0:35996:36098  "market.liquidatorGate == address(0) || ILiquidatorGate(market.liquidatorGate).canLiquidate(msg.sender)"
                        if iszero(expr_47)
                        {
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let _159 := and(/** @src 0:36051:36072  "market.liquidatorGate" */ read_from_calldatat_address(/** @src 0:35996:36017  "market.liquidatorGate" */ add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(4), 228)), 0xffffffffffffffffffffffffffffffffffffffff)
                            /// @src 0:36035:36098  "ILiquidatorGate(market.liquidatorGate).canLiquidate(msg.sender)"
                            let _160 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                            /// @src 0:36035:36098  "ILiquidatorGate(market.liquidatorGate).canLiquidate(msg.sender)"
                            mstore(_160, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(224, 0xb9f4ff55))
                            mstore(/** @src 0:36035:36098  "ILiquidatorGate(market.liquidatorGate).canLiquidate(msg.sender)" */ add(_160, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 4), /** @src 0:36087:36097  "msg.sender" */ caller())
                            /// @src 0:36035:36098  "ILiquidatorGate(market.liquidatorGate).canLiquidate(msg.sender)"
                            let _161 := staticcall(gas(), _159, _160, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 36, /** @src 0:36035:36098  "ILiquidatorGate(market.liquidatorGate).canLiquidate(msg.sender)" */ _160, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32)
                            /// @src 0:36035:36098  "ILiquidatorGate(market.liquidatorGate).canLiquidate(msg.sender)"
                            if iszero(_161)
                            {
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                let pos_9 := mload(64)
                                returndatacopy(pos_9, mload(0x0320), returndatasize())
                                revert(pos_9, returndatasize())
                            }
                            /// @src 0:36035:36098  "ILiquidatorGate(market.liquidatorGate).canLiquidate(msg.sender)"
                            let expr_48 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x0320)
                            /// @src 0:36035:36098  "ILiquidatorGate(market.liquidatorGate).canLiquidate(msg.sender)"
                            if _161
                            {
                                let _162 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32
                                /// @src 0:36035:36098  "ILiquidatorGate(market.liquidatorGate).canLiquidate(msg.sender)"
                                if gt(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32, /** @src 0:36035:36098  "ILiquidatorGate(market.liquidatorGate).canLiquidate(msg.sender)" */ returndatasize()) { _162 := returndatasize() }
                                finalize_allocation(_160, _162)
                                expr_48 := abi_decode_bool_fromMemory(_160, add(_160, _162))
                            }
                            /// @src 0:35996:36098  "market.liquidatorGate == address(0) || ILiquidatorGate(market.liquidatorGate).canLiquidate(msg.sender)"
                            expr_47 := expr_48
                        }
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        if iszero(expr_47)
                        {
                            mstore(mload(0x0320), shl(224, 0x37a4840b))
                            revert(mload(0x0320), 4)
                        }
                        /// @src 0:36165:36180  "uint256 maxDebt"
                        let var_maxDebt := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x0320)
                        /// @src 0:36165:36180  "uint256 maxDebt"
                        var_maxDebt := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x0320)
                        /// @src 0:36190:36219  "uint256 liquidatedCollatPrice"
                        let var_liquidatedCollatPrice := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x0320)
                        /// @src 0:36190:36219  "uint256 liquidatedCollatPrice"
                        var_liquidatedCollatPrice := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x0320)
                        /// @src 0:36276:36306  "uint256 badDebt = originalDebt"
                        let var_badDebt := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(_158, 0xffffffffffffffffffffffffffffffff)
                        /// @src 0:36316:36370  "uint128 _collateralBitmap = _position.collateralBitmap"
                        mstore(0x02c0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shr(128, _158))
                        /// @src 0:36380:37161  "while (_collateralBitmap != 0) {..."
                        for { }
                        /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:36387:36409  "_collateralBitmap != 0" */ mload(0x02c0), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)
                        /// @src 0:36380:37161  "while (_collateralBitmap != 0) {..."
                        { }
                        {
                            /// @src 0:36525:36548  "market.collateralParams"
                            let expr_offset, expr_length := access_calldata_tail_array_struct_CollateralParams_calldata_dyn_calldata(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ add(4, calldataload(4)), /** @src 0:36525:36548  "market.collateralParams" */ add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(4), 100))
                            let converted_1 := abi_decode_struct_CollateralParams(/** @src 0:36525:36551  "market.collateralParams[i]" */ calldata_array_index_access_struct_CollateralParams_calldata_dyn_calldata(expr_offset, expr_length, /** @src 12:1643:1704  "assembly {..." */ sub(255, clz(/** @src 0:36437:36468  "UtilsLib.msb(_collateralBitmap)" */ mload(0x02c0)))), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldatasize())
                            let cleaned_70 := and(mload(/** @src 0:36589:36612  "_collateralParam.oracle" */ add(converted_1, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 96)), 0xffffffffffffffffffffffffffffffffffffffff)
                            /// @src 0:36581:36621  "IOracle(_collateralParam.oracle).price()"
                            let _163 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                            /// @src 0:36581:36621  "IOracle(_collateralParam.oracle).price()"
                            mstore(_163, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(225, 0x501ad8ff))
                            /// @src 0:36581:36621  "IOracle(_collateralParam.oracle).price()"
                            let _164 := staticcall(gas(), cleaned_70, _163, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 4, /** @src 0:36581:36621  "IOracle(_collateralParam.oracle).price()" */ _163, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32)
                            /// @src 0:36581:36621  "IOracle(_collateralParam.oracle).price()"
                            if iszero(_164)
                            {
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                let pos_10 := mload(64)
                                returndatacopy(pos_10, mload(0x0320), returndatasize())
                                revert(pos_10, returndatasize())
                            }
                            /// @src 0:36581:36621  "IOracle(_collateralParam.oracle).price()"
                            let expr_49 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x0320)
                            /// @src 0:36581:36621  "IOracle(_collateralParam.oracle).price()"
                            if _164
                            {
                                let _165 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32
                                /// @src 0:36581:36621  "IOracle(_collateralParam.oracle).price()"
                                if gt(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _165, /** @src 0:36581:36621  "IOracle(_collateralParam.oracle).price()" */ returndatasize()) { _165 := returndatasize() }
                                finalize_allocation(_163, _165)
                                let value0_15 := /** @src -1:-1:-1 */ 0
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                if slt(sub(/** @src 0:36581:36621  "IOracle(_collateralParam.oracle).price()" */ add(_163, _165), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _163), 32)
                                {
                                    revert(/** @src -1:-1:-1 */ 0, 0)
                                }
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                value0_15 := mload(_163)
                                /// @src 0:36581:36621  "IOracle(_collateralParam.oracle).price()"
                                expr_49 := value0_15
                            }
                            /// @src 0:36635:36690  "if (i == collateralIndex) liquidatedCollatPrice = price"
                            if /** @src 0:36639:36659  "i == collateralIndex" */ eq(/** @src 12:1643:1704  "assembly {..." */ sub(255, clz(/** @src 0:36437:36468  "UtilsLib.msb(_collateralBitmap)" */ mload(0x02c0))), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(36))
                            /// @src 0:36635:36690  "if (i == collateralIndex) liquidatedCollatPrice = price"
                            {
                                /// @src 0:36661:36690  "liquidatedCollatPrice = price"
                                var_liquidatedCollatPrice := expr_49
                            }
                            /// @src 0:36726:36749  "_position.collateral[i]"
                            let _166, _167 := storage_array_index_access_uint128_(/** @src 0:36726:36746  "_position.collateral" */ add(/** @src 0:35756:35778  "position[id][borrower]" */ dataSlot_35, /** @src 0:36726:36746  "_position.collateral" */ 3), /** @src 12:1643:1704  "assembly {..." */ sub(255, clz(/** @src 0:36437:36468  "UtilsLib.msb(_collateralBitmap)" */ mload(0x02c0))))
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let value_36 := and(shr(shl(/** @src 0:36726:36746  "_position.collateral" */ 3, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _167), sload(/** @src 0:36726:36749  "_position.collateral[i]" */ _166)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)
                            let r_4 := div(/** @src 12:653:658  "x * y" */ checked_mul_uint256(/** @src 0:36774:36823  "_collateral.mulDivDown(price, ORACLE_PRICE_SCALE)" */ value_36, expr_49), /** @src 7:234:238  "1e36" */ 0xc097ce7bc90715b34b9f1000000000)
                            /// @src 12:653:658  "x * y"
                            let _168 := checked_mul_uint256(r_4, /** @src 7:234:238  "1e36" */ mload(/** @src 0:36835:36856  "_collateralParam.lltv" */ add(converted_1, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32)))
                            /// @src 12:652:663  "(x * y) / d"
                            let r_5 := /** @src -1:-1:-1 */ mload(0x0320)
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let _169 := mload(0x0320)
                            _169 := /** @src -1:-1:-1 */ mload(0x0320)
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            r_5 := div(_168, /** @src 7:190:194  "1e18" */ 0x0de0b6b3a7640000)
                            /// @src 0:36763:36862  "maxDebt += _collateral.mulDivDown(price, ORACLE_PRICE_SCALE).mulDivDown(_collateralParam.lltv, WAD)"
                            var_maxDebt := checked_add_uint256(var_maxDebt, /** @src 0:36774:36862  "_collateral.mulDivDown(price, ORACLE_PRICE_SCALE).mulDivDown(_collateralParam.lltv, WAD)" */ r_5)
                            /// @src 12:822:837  "x * y + (d - 1)"
                            let _170 := checked_add_uint256_44170(/** @src 12:822:827  "x * y" */ checked_mul_uint256(value_36, expr_49))
                            /// @src 12:821:842  "(x * y + (d - 1)) / d"
                            let r_6 := /** @src -1:-1:-1 */ mload(0x0320)
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let _171 := mload(0x0320)
                            _171 := /** @src -1:-1:-1 */ mload(0x0320)
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            r_6 := div(_170, /** @src 7:234:238  "1e36" */ 0xc097ce7bc90715b34b9f1000000000)
                            let _172 := mload(/** @src 0:36835:36856  "_collateralParam.lltv" */ add(converted_1, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32))
                            /// @src 0:37007:37072  "maxLif(_collateralParam.lltv, _collateralParam.liquidationCursor)"
                            let _173 := fun_maxLif(_172, /** @src 7:234:238  "1e36" */ mload(/** @src 0:37037:37071  "_collateralParam.liquidationCursor" */ add(converted_1, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 64)))
                            /// @src 12:822:827  "x * y"
                            let expr_50 := checked_mul_uint256_44172(r_6)
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let diff_1 := add(_173, not(0))
                            if gt(diff_1, _173)
                            {
                                mstore(mload(0x0320), shl(224, 0x4e487b71))
                                mstore(4, 0x11)
                                revert(mload(0x0320), 36)
                            }
                            /// @src 12:814:842  "return (x * y + (d - 1)) / d"
                            let var_3 := /** @src 12:821:842  "(x * y + (d - 1)) / d" */ checked_div_uint256(/** @src 12:822:837  "x * y + (d - 1)" */ checked_add_uint256(expr_50, /** @src 12:831:836  "d - 1" */ diff_1), /** @src 12:821:842  "(x * y + (d - 1)) / d" */ _173)
                            /// @src 0:36876:37087  "badDebt = badDebt.zeroFloorSub(..."
                            var_badDebt := /** @src 12:429:491  "assembly {..." */ mul(gt(var_badDebt, var_3), sub(var_badDebt, var_3))
                            /// @src 0:37101:37150  "_collateralBitmap = _collateralBitmap.clearBit(i)"
                            mstore(0x02c0, /** @src 12:2170:2190  "bitmap & ~(1 << bit)" */ and(and(/** @src 0:36387:36409  "_collateralBitmap != 0" */ mload(0x02c0), /** @src 12:2179:2190  "~(1 << bit)" */ not(/** @src 7:892:894  "16" */ shl(/** @src 12:1643:1704  "assembly {..." */ sub(255, clz(/** @src 0:36437:36468  "UtilsLib.msb(_collateralBitmap)" */ mload(0x02c0))), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 1))), 0xffffffffffffffffffffffffffffffff))
                        }
                        /// @src 12:2888:2920  "abi.encode(key1, key2, baseSlot)"
                        let expr_mpos_4 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                        /// @src 12:2888:2920  "abi.encode(key1, key2, baseSlot)"
                        let tail_15 := /** @src -1:-1:-1 */ mload(0x0320)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        tail_15 := add(/** @src 12:2888:2920  "abi.encode(key1, key2, baseSlot)" */ expr_mpos_4, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 128)
                        mstore(/** @src 12:2888:2920  "abi.encode(key1, key2, baseSlot)" */ add(expr_mpos_4, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32), mload(0x0300))
                        mstore(add(/** @src 12:2888:2920  "abi.encode(key1, key2, baseSlot)" */ expr_mpos_4, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 64), and(value4_2, 0xffffffffffffffffffffffffffffffffffffffff))
                        mstore(add(/** @src 12:2888:2920  "abi.encode(key1, key2, baseSlot)" */ expr_mpos_4, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 96), /** @src 7:945:991  "keccak256(\"morpho.midnight.liquidationLocked\")" */ 0x90e10dad8320b2f9ee6b84bebe89829c27a3fc1209e68031bc1d4b65c22e4da4)
                        /// @src 12:2888:2920  "abi.encode(key1, key2, baseSlot)"
                        mstore(expr_mpos_4, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 96)
                        /// @src 12:2888:2920  "abi.encode(key1, key2, baseSlot)"
                        finalize_allocation(expr_mpos_4, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 128)
                        /// @src 0:37192:37323  "!liquidationLocked(id, borrower)..."
                        let expr_51 := /** @src 0:37192:37224  "!liquidationLocked(id, borrower)" */ iszero(/** @src 12:2932:3001  "assembly (\"memory-safe\") {..." */ tload(/** @src 12:2878:2921  "keccak256(abi.encode(key1, key2, baseSlot))" */ keccak256(/** @src 12:2888:2920  "abi.encode(key1, key2, baseSlot)" */ add(expr_mpos_4, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32), mload(/** @src 12:2878:2921  "keccak256(abi.encode(key1, key2, baseSlot))" */ expr_mpos_4))))
                        /// @src 0:37192:37323  "!liquidationLocked(id, borrower)..."
                        if expr_51
                        {
                            /// @src 0:37245:37322  "postMaturityMode ? block.timestamp > market.maturity : originalDebt > maxDebt"
                            let expr_52 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x0320)
                            /// @src 0:37245:37322  "postMaturityMode ? block.timestamp > market.maturity : originalDebt > maxDebt"
                            switch value_34
                            case 0 {
                                expr_52 := /** @src 0:37300:37322  "originalDebt > maxDebt" */ gt(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(_158, 0xffffffffffffffffffffffffffffffff), /** @src 0:37300:37322  "originalDebt > maxDebt" */ var_maxDebt)
                            }
                            default /// @src 0:37245:37322  "postMaturityMode ? block.timestamp > market.maturity : originalDebt > maxDebt"
                            {
                                expr_52 := /** @src 0:37264:37297  "block.timestamp > market.maturity" */ gt(/** @src 0:37264:37279  "block.timestamp" */ timestamp(), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(/** @src 0:37282:37297  "market.maturity" */ add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(4), 132)))
                            }
                            /// @src 0:37192:37323  "!liquidationLocked(id, borrower)..."
                            expr_51 := expr_52
                        }
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        if iszero(expr_51)
                        {
                            mstore(mload(0x0320), shl(225, 0x6ef5bcdd))
                            revert(mload(0x0320), 4)
                        }
                        /// @src 0:37375:38241  "if (badDebt > 0) {..."
                        if /** @src 0:37379:37390  "badDebt > 0" */ iszero(iszero(var_badDebt))
                        /// @src 0:37375:38241  "if (badDebt > 0) {..."
                        {
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            sstore(/** @src 0:35873:35887  "_position.debt" */ add(/** @src 0:35756:35778  "position[id][borrower]" */ dataSlot_35, /** @src 0:35873:35887  "_position.debt" */ 2), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ or(and(sload(/** @src 0:35873:35887  "_position.debt" */ add(/** @src 0:35756:35778  "position[id][borrower]" */ dataSlot_35, /** @src 0:35873:35887  "_position.debt" */ 2)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(0xffffffffffffffffffffffffffffffff)), and(/** @src 0:37497:37531  "_position.debt -= uint128(badDebt)" */ checked_sub_uint128(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(_158, 0xffffffffffffffffffffffffffffffff), and(/** @src 0:37515:37531  "uint128(badDebt)" */ var_badDebt, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)), 0xffffffffffffffffffffffffffffffff)))
                            let _174 := sload(/** @src 0:37567:37590  "_marketState.totalUnits" */ mload(0x02a0))
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let cleaned_71 := and(_174, 0xffffffffffffffffffffffffffffffff)
                            /// @src 0:37746:37777  "type(uint128).max - _lossFactor"
                            let expr_53 := checked_sub_uint256_44174(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shr(128, _174))
                            /// @src 0:37663:37839  "_marketState.lossFactor = UtilsLib.toUint128(..."
                            update_storage_value_offset_uint128_to_uint128(mload(0x02a0), /** @src 0:37689:37839  "UtilsLib.toUint128(..." */ fun_toUint128(/** @src 0:37725:37825  "type(uint128).max - (type(uint128).max - _lossFactor).mulDivDown(_totalUnits - badDebt, _totalUnits)" */ checked_sub_uint256_44174(/** @src 12:652:663  "(x * y) / d" */ checked_div_uint256(/** @src 12:653:658  "x * y" */ checked_mul_uint256(expr_53, /** @src 0:37790:37811  "_totalUnits - badDebt" */ checked_sub_uint256(cleaned_71, var_badDebt)), /** @src 12:652:663  "(x * y) / d" */ cleaned_71))))
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            sstore(/** @src 0:37853:37907  "_marketState.totalUnits -= UtilsLib.toUint128(badDebt)" */ mload(0x02a0), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ or(and(sload(/** @src 0:37853:37907  "_marketState.totalUnits -= UtilsLib.toUint128(badDebt)" */ mload(0x02a0)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(0xffffffffffffffffffffffffffffffff)), and(/** @src 0:37853:37907  "_marketState.totalUnits -= UtilsLib.toUint128(badDebt)" */ checked_sub_uint128(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(sload(/** @src 0:37853:37907  "_marketState.totalUnits -= UtilsLib.toUint128(badDebt)" */ mload(0x02a0)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff), /** @src 0:37880:37907  "UtilsLib.toUint128(badDebt)" */ fun_toUint128(var_badDebt)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)))
                            /// @src 0:37956:38230  "_lossFactor < type(uint128).max..."
                            let expr_54 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x0320)
                            /// @src 0:37956:38230  "_lossFactor < type(uint128).max..."
                            switch /** @src 0:37956:37987  "_lossFactor < type(uint128).max" */ lt(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shr(128, _174), 0xffffffffffffffffffffffffffffffff)
                            case /** @src 0:37956:38230  "_lossFactor < type(uint128).max..." */ 0 {
                                expr_54 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x0320)
                            }
                            default /// @src 0:37956:38230  "_lossFactor < type(uint128).max..."
                            {
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                let _175 := shr(128, sload(/** @src 0:38046:38078  "_marketState.continuousFeeCredit" */ add(mload(0x02a0), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 1)))
                                let diff_2 := sub(0xffffffffffffffffffffffffffffffff, shr(128, sload(/** @src 0:38135:38158  "_marketState.lossFactor" */ mload(0x02a0))))
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                if gt(diff_2, 0xffffffffffffffffffffffffffffffff)
                                {
                                    mstore(mload(0x0320), shl(224, 0x4e487b71))
                                    mstore(4, 0x11)
                                    revert(mload(0x0320), 36)
                                }
                                /// @src 0:37956:38230  "_lossFactor < type(uint128).max..."
                                expr_54 := /** @src 0:38006:38210  "UtilsLib.toUint128(..." */ fun_toUint128(/** @src 12:652:663  "(x * y) / d" */ checked_div_uint256(/** @src 12:653:658  "x * y" */ checked_mul_uint256(_175, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:38046:38192  "_marketState.continuousFeeCredit..." */ diff_2, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)), /** @src 0:38160:38191  "type(uint128).max - _lossFactor" */ checked_sub_uint256_44174(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shr(128, _174))))
                            }
                            /// @src 0:37921:38230  "_marketState.continuousFeeCredit = _lossFactor < type(uint128).max..."
                            update_storage_value_offset_uint128_to_uint128(/** @src 0:37921:37953  "_marketState.continuousFeeCredit" */ add(mload(0x02a0), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 1), /** @src 0:37921:38230  "_marketState.continuousFeeCredit = _lossFactor < type(uint128).max..." */ expr_54)
                        }
                        /// @src 0:38255:38290  "repaidUnits > 0 || seizedAssets > 0"
                        let expr_55 := _157
                        if expr_46
                        {
                            expr_55 := /** @src 0:38274:38290  "seizedAssets > 0" */ iszero(iszero(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(68)))
                        }
                        /// @src 0:38251:40269  "if (repaidUnits > 0 || seizedAssets > 0) {..."
                        if expr_55
                        {
                            /// @src 0:38321:38344  "market.collateralParams"
                            let expr_offset_1, expr_length_1 := access_calldata_tail_array_struct_CollateralParams_calldata_dyn_calldata(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ add(4, calldataload(4)), /** @src 0:36525:36548  "market.collateralParams" */ add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(4), 100))
                            let value_37 := calldataload(/** @src 0:38321:38366  "market.collateralParams[collateralIndex].lltv" */ add(/** @src 0:38321:38361  "market.collateralParams[collateralIndex]" */ calldata_array_index_access_struct_CollateralParams_calldata_dyn_calldata(expr_offset_1, expr_length_1, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(36)), 32))
                            /// @src 0:38411:38434  "market.collateralParams"
                            let expr_offset_2, expr_length_2 := access_calldata_tail_array_struct_CollateralParams_calldata_dyn_calldata(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ add(4, calldataload(4)), /** @src 0:36525:36548  "market.collateralParams" */ add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(4), 100))
                            /// @src 0:38398:38470  "maxLif(lltv, market.collateralParams[collateralIndex].liquidationCursor)"
                            let expr_56 := fun_maxLif(value_37, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(/** @src 0:38411:38469  "market.collateralParams[collateralIndex].liquidationCursor" */ add(/** @src 0:38411:38451  "market.collateralParams[collateralIndex]" */ calldata_array_index_access_struct_CollateralParams_calldata_dyn_calldata(expr_offset_2, expr_length_2, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(36)), 64)))
                            /// @src 0:38498:38659  "postMaturityMode..."
                            let expr_57 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x0320)
                            /// @src 0:38498:38659  "postMaturityMode..."
                            switch value_34
                            case 0 { expr_57 := expr_56 }
                            default {
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                if gt(add(expr_56, not(0x0de0b6b3a763ffff)), expr_56)
                                {
                                    mstore(mload(0x0320), shl(224, 0x4e487b71))
                                    mstore(4, 0x11)
                                    revert(mload(0x0320), 36)
                                }
                                /// @src 7:892:894  "16"
                                let sum := add(/** @src 7:190:194  "1e18" */ 0x0de0b6b3a7640000, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ div(/** @src 0:38561:38614  "(_maxLif - WAD) * (block.timestamp - market.maturity)" */ checked_mul_uint256(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ add(expr_56, not(0x0de0b6b3a763ffff)), /** @src 0:38580:38613  "block.timestamp - market.maturity" */ checked_sub_uint256(/** @src 0:38580:38595  "block.timestamp" */ timestamp(), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(/** @src 0:38598:38613  "market.maturity" */ add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(4), 132)))), /** @src 7:792:802  "60 minutes" */ 0x0e10))
                                /// @src 7:892:894  "16"
                                if gt(/** @src 7:190:194  "1e18" */ 0x0de0b6b3a7640000, /** @src 7:892:894  "16" */ sum)
                                {
                                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                    mstore(mload(0x0320), shl(224, 0x4e487b71))
                                    mstore(4, 0x11)
                                    revert(mload(0x0320), 36)
                                }
                                /// @src 0:38498:38659  "postMaturityMode..."
                                expr_57 := /** @src 12:259:329  "assembly {..." */ xor(expr_56, mul(xor(expr_56, sum), lt(sum, expr_56)))
                            }
                            /// @src 0:38674:38966  "if (seizedAssets > 0) {..."
                            switch /** @src 0:38678:38694  "seizedAssets > 0" */ iszero(iszero(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(68)))
                            case /** @src 0:38674:38966  "if (seizedAssets > 0) {..." */ 0 {
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                let r_7 := div(/** @src 12:653:658  "x * y" */ checked_mul_uint256(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(100), /** @src 0:38865:38897  "repaidUnits.mulDivDown(lif, WAD)" */ expr_57), /** @src 7:190:194  "1e18" */ 0x0de0b6b3a7640000)
                                /// @src 12:653:658  "x * y"
                                let product := /** @src -1:-1:-1 */ mload(0x0320)
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                product := mul(r_7, /** @src 7:234:238  "1e36" */ 0xc097ce7bc90715b34b9f1000000000)
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                if iszero(or(iszero(r_7), eq(/** @src 7:234:238  "1e36" */ 0xc097ce7bc90715b34b9f1000000000, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ div(product, r_7))))
                                {
                                    mstore(mload(0x0320), shl(224, 0x4e487b71))
                                    mstore(4, 0x11)
                                    revert(mload(0x0320), 36)
                                }
                                /// @src 0:38850:38951  "seizedAssets = repaidUnits.mulDivDown(lif, WAD).mulDivDown(ORACLE_PRICE_SCALE, liquidatedCollatPrice)"
                                mstore(0x0280, /** @src 12:652:663  "(x * y) / d" */ checked_div_uint256(/** @src 12:653:658  "x * y" */ product, /** @src 12:652:663  "(x * y) / d" */ var_liquidatedCollatPrice))
                            }
                            default /// @src 0:38674:38966  "if (seizedAssets > 0) {..."
                            {
                                /// @src 12:822:837  "x * y + (d - 1)"
                                let _176 := checked_add_uint256_44170(/** @src 12:822:827  "x * y" */ checked_mul_uint256(mload(0x0280), var_liquidatedCollatPrice))
                                /// @src 12:821:842  "(x * y + (d - 1)) / d"
                                let r_8 := /** @src -1:-1:-1 */ mload(0x0320)
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                let _177 := mload(0x0320)
                                _177 := /** @src -1:-1:-1 */ mload(0x0320)
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                r_8 := div(_176, /** @src 7:234:238  "1e36" */ 0xc097ce7bc90715b34b9f1000000000)
                                /// @src 12:822:827  "x * y"
                                let expr_58 := checked_mul_uint256_44172(r_8)
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                if gt(add(expr_57, not(0)), expr_57)
                                {
                                    mstore(mload(0x0320), shl(224, 0x4e487b71))
                                    mstore(4, 0x11)
                                    revert(mload(0x0320), 36)
                                }
                                /// @src 0:38714:38811  "repaidUnits = seizedAssets.mulDivUp(liquidatedCollatPrice, ORACLE_PRICE_SCALE).mulDivUp(WAD, lif)"
                                mstore(0x0260, /** @src 12:821:842  "(x * y + (d - 1)) / d" */ checked_div_uint256(/** @src 12:822:837  "x * y + (d - 1)" */ checked_add_uint256(expr_58, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ add(expr_57, not(0))), /** @src 12:821:842  "(x * y + (d - 1)) / d" */ expr_57))
                            }
                            /// @src 0:38984:39015  "!postMaturityMode && lltv < WAD"
                            let expr_59 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ iszero(value_34)
                            /// @src 0:38984:39015  "!postMaturityMode && lltv < WAD"
                            if /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ iszero(value_34)
                            /// @src 0:38984:39015  "!postMaturityMode && lltv < WAD"
                            {
                                expr_59 := /** @src 0:39005:39015  "lltv < WAD" */ lt(value_37, /** @src 7:190:194  "1e18" */ 0x0de0b6b3a7640000)
                            }
                            /// @src 0:38980:39773  "if (!postMaturityMode && lltv < WAD) {..."
                            if expr_59
                            {
                                /// @src 0:39295:39319  "_position.debt - maxDebt"
                                let expr_60 := checked_sub_uint256(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(sload(/** @src 0:35873:35887  "_position.debt" */ add(/** @src 0:35756:35778  "position[id][borrower]" */ dataSlot_35, /** @src 0:35873:35887  "_position.debt" */ 2)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff), /** @src 0:39295:39319  "_position.debt - maxDebt" */ var_maxDebt)
                                /// @src 0:39353:39363  "lif * lltv"
                                let _178 := checked_mul_uint256(expr_57, value_37)
                                /// @src 0:39341:39363  "WAD * WAD - lif * lltv"
                                let diff_3 := /** @src -1:-1:-1 */ mload(0x0320)
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                diff_3 := sub(/** @src 7:234:238  "1e36" */ 0xc097ce7bc90715b34b9f1000000000, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _178)
                                if gt(diff_3, /** @src 7:234:238  "1e36" */ 0xc097ce7bc90715b34b9f1000000000)
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                {
                                    mstore(mload(0x0320), shl(224, 0x4e487b71))
                                    mstore(4, 0x11)
                                    revert(mload(0x0320), 36)
                                }
                                /// @src 0:39294:39364  "(_position.debt - maxDebt).mulDivUp(WAD * WAD, WAD * WAD - lif * lltv)"
                                let var_4 := /** @src -1:-1:-1 */ mload(0x0320)
                                /// @src 12:822:827  "x * y"
                                let product_1 := /** @src -1:-1:-1 */ 0
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                product_1 := mul(/** @src 12:822:827  "x * y" */ expr_60, /** @src 7:234:238  "1e36" */ 0xc097ce7bc90715b34b9f1000000000)
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                if iszero(or(iszero(/** @src 12:822:827  "x * y" */ expr_60), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ eq(/** @src 7:234:238  "1e36" */ 0xc097ce7bc90715b34b9f1000000000, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ div(product_1, /** @src 12:822:827  "x * y" */ expr_60))))
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                {
                                    mstore(0, shl(224, 0x4e487b71))
                                    mstore(4, 0x11)
                                    revert(0, 0x24)
                                }
                                if gt(add(diff_3, not(0)), diff_3)
                                {
                                    mstore(/** @src -1:-1:-1 */ mload(0x0320), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(224, 0x4e487b71))
                                    mstore(4, 0x11)
                                    revert(/** @src -1:-1:-1 */ mload(0x0320), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 36)
                                }
                                /// @src 12:814:842  "return (x * y + (d - 1)) / d"
                                var_4 := /** @src 12:821:842  "(x * y + (d - 1)) / d" */ checked_div_uint256(/** @src 12:822:837  "x * y + (d - 1)" */ checked_add_uint256(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ product_1, add(diff_3, not(0))), /** @src 12:821:842  "(x * y + (d - 1)) / d" */ diff_3)
                                /// @src 0:39411:39435  "repaidUnits <= maxRepaid"
                                let _179 := gt(mload(0x0260), var_4)
                                /// @src 0:39411:39679  "repaidUnits <= maxRepaid..."
                                let expr_61 := /** @src 0:39411:39435  "repaidUnits <= maxRepaid" */ iszero(_179)
                                /// @src 0:39411:39679  "repaidUnits <= maxRepaid..."
                                if _179
                                {
                                    /// @src 0:39463:39500  "_position.collateral[collateralIndex]"
                                    let _180, _181 := storage_array_index_access_uint128_(/** @src 0:36726:36746  "_position.collateral" */ add(/** @src 0:35756:35778  "position[id][borrower]" */ dataSlot_35, /** @src 0:36726:36746  "_position.collateral" */ 3), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(36))
                                    /// @src 12:653:658  "x * y"
                                    let _182 := checked_mul_uint256(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(shr(shl(/** @src 0:36726:36746  "_position.collateral" */ 3, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _181), sload(/** @src 0:39463:39500  "_position.collateral[collateralIndex]" */ _180)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff), /** @src 12:653:658  "x * y" */ var_liquidatedCollatPrice)
                                    /// @src 12:652:663  "(x * y) / d"
                                    let r_9 := /** @src -1:-1:-1 */ mload(0x0320)
                                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                    let _183 := mload(0x0320)
                                    _183 := /** @src -1:-1:-1 */ mload(0x0320)
                                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                    r_9 := div(_182, /** @src 7:234:238  "1e36" */ 0xc097ce7bc90715b34b9f1000000000)
                                    /// @src 12:645:663  "return (x * y) / d"
                                    let var_5 := /** @src 12:652:663  "(x * y) / d" */ checked_div_uint256(/** @src 12:653:658  "x * y" */ checked_mul_uint256_44172(r_9), /** @src 12:652:663  "(x * y) / d" */ expr_57)
                                    /// @src 0:39411:39679  "repaidUnits <= maxRepaid..."
                                    expr_61 := /** @src 0:39463:39679  "_position.collateral[collateralIndex].mulDivDown(liquidatedCollatPrice, ORACLE_PRICE_SCALE)..." */ lt(/** @src 12:429:491  "assembly {..." */ mul(gt(var_5, var_4), sub(var_5, var_4)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(/** @src 0:39660:39679  "market.rcfThreshold" */ add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(4), 164)))
                                }
                                /// @src 7:792:802  "60 minutes"
                                if iszero(expr_61)
                                {
                                    mstore(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x0320), /** @src 7:792:802  "60 minutes" */ shl(227, 0x036851d1))
                                    revert(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x0320), 4)
                                }
                            }
                            /// @src 0:39811:39848  "_position.collateral[collateralIndex]"
                            let _184, _185 := storage_array_index_access_uint128_(/** @src 0:36726:36746  "_position.collateral" */ add(/** @src 0:35756:35778  "position[id][borrower]" */ dataSlot_35, /** @src 0:36726:36746  "_position.collateral" */ 3), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(36))
                            let value_38 := and(shr(shl(/** @src 0:36726:36746  "_position.collateral" */ 3, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _185), sload(/** @src 0:39811:39848  "_position.collateral[collateralIndex]" */ _184)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)
                            /// @src 0:39811:39883  "_position.collateral[collateralIndex] - UtilsLib.toUint128(seizedAssets)"
                            let expr_62 := checked_sub_uint128(value_38, /** @src 0:39851:39883  "UtilsLib.toUint128(seizedAssets)" */ fun_toUint128(mload(0x0280)))
                            /// @src 0:39897:39934  "_position.collateral[collateralIndex]"
                            let _186, _187 := storage_array_index_access_uint128_(/** @src 0:36726:36746  "_position.collateral" */ add(/** @src 0:35756:35778  "position[id][borrower]" */ dataSlot_35, /** @src 0:36726:36746  "_position.collateral" */ 3), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(36))
                            /// @src 0:39897:39950  "_position.collateral[collateralIndex] = newCollateral"
                            update_storage_value_uint128_to_uint128(_186, _187, expr_62)
                            /// @src 0:39968:40006  "newCollateral == 0 && seizedAssets > 0"
                            let expr_63 := /** @src 0:39968:39986  "newCollateral == 0" */ iszero(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:39968:39986  "newCollateral == 0" */ expr_62, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff))
                            /// @src 0:39968:40006  "newCollateral == 0 && seizedAssets > 0"
                            if expr_63
                            {
                                expr_63 := /** @src 0:39990:40006  "seizedAssets > 0" */ iszero(iszero(mload(0x0280)))
                            }
                            /// @src 0:39964:40122  "if (newCollateral == 0 && seizedAssets > 0) {..."
                            if expr_63
                            {
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                let _188 := shr(128, sload(/** @src 0:35873:35887  "_position.debt" */ add(/** @src 0:35756:35778  "position[id][borrower]" */ dataSlot_35, /** @src 0:35873:35887  "_position.debt" */ 2)))
                                /// @src 0:40055:40107  "_position.collateralBitmap.clearBit(collateralIndex)"
                                let var_6 := /** @src -1:-1:-1 */ 0
                                /// @src 12:2155:2191  "return uint128(bitmap & ~(1 << bit))"
                                var_6 := /** @src 12:2170:2190  "bitmap & ~(1 << bit)" */ and(and(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _188, /** @src 12:2179:2190  "~(1 << bit)" */ not(/** @src 7:892:894  "16" */ shl(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(36), /** @src 12:2181:2182  "1" */ 0x01))), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)
                                /// @src 0:40026:40107  "_position.collateralBitmap = _position.collateralBitmap.clearBit(collateralIndex)"
                                update_storage_value_offset_uint128_to_uint128(/** @src 0:35873:35887  "_position.debt" */ add(/** @src 0:35756:35778  "position[id][borrower]" */ dataSlot_35, /** @src 0:35873:35887  "_position.debt" */ 2), /** @src 0:40055:40107  "_position.collateralBitmap.clearBit(collateralIndex)" */ var_6)
                            }
                            /// @src 0:40164:40195  "UtilsLib.toUint128(repaidUnits)"
                            let expr_64 := fun_toUint128(mload(0x0260))
                            /// @src 0:40135:40160  "_marketState.withdrawable"
                            let _189 := add(mload(0x02a0), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 1)
                            sstore(/** @src 0:40135:40195  "_marketState.withdrawable += UtilsLib.toUint128(repaidUnits)" */ _189, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ or(and(sload(/** @src 0:40135:40195  "_marketState.withdrawable += UtilsLib.toUint128(repaidUnits)" */ _189), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(0xffffffffffffffffffffffffffffffff)), and(/** @src 0:40135:40195  "_marketState.withdrawable += UtilsLib.toUint128(repaidUnits)" */ checked_add_uint128(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(sload(/** @src 0:40135:40195  "_marketState.withdrawable += UtilsLib.toUint128(repaidUnits)" */ _189), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff), /** @src 0:40135:40195  "_marketState.withdrawable += UtilsLib.toUint128(repaidUnits)" */ expr_64), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)))
                            sstore(/** @src 0:35873:35887  "_position.debt" */ add(/** @src 0:35756:35778  "position[id][borrower]" */ dataSlot_35, /** @src 0:35873:35887  "_position.debt" */ 2), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ or(and(sload(/** @src 0:35873:35887  "_position.debt" */ add(/** @src 0:35756:35778  "position[id][borrower]" */ dataSlot_35, /** @src 0:35873:35887  "_position.debt" */ 2)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(0xffffffffffffffffffffffffffffffff)), and(/** @src 0:40209:40258  "_position.debt -= UtilsLib.toUint128(repaidUnits)" */ checked_sub_uint128(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(sload(/** @src 0:35873:35887  "_position.debt" */ add(/** @src 0:35756:35778  "position[id][borrower]" */ dataSlot_35, /** @src 0:35873:35887  "_position.debt" */ 2)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff), /** @src 0:40227:40258  "UtilsLib.toUint128(repaidUnits)" */ fun_toUint128(mload(0x0260))), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)))
                        }
                        /// @src 0:40295:40341  "callback != address(0) ? callback : msg.sender"
                        let expr_65 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x0320)
                        /// @src 0:40295:40341  "callback != address(0) ? callback : msg.sender"
                        switch /** @src 0:40295:40317  "callback != address(0)" */ iszero(iszero(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(mload(0x02e0), 0xffffffffffffffffffffffffffffffffffffffff)))
                        case /** @src 0:40295:40341  "callback != address(0) ? callback : msg.sender" */ 0 {
                            expr_65 := /** @src 0:40331:40341  "msg.sender" */ caller()
                        }
                        default /// @src 0:40295:40341  "callback != address(0) ? callback : msg.sender"
                        { expr_65 := mload(0x02e0) }
                        /// @src 0:40430:40453  "market.collateralParams"
                        let expr_offset_3, expr_length_3 := access_calldata_tail_array_struct_CollateralParams_calldata_dyn_calldata(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ add(4, calldataload(4)), /** @src 0:36525:36548  "market.collateralParams" */ add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(4), 100))
                        /// @src 0:40430:40476  "market.collateralParams[collateralIndex].token"
                        let expr_66 := read_from_calldatat_address(/** @src 0:40430:40470  "market.collateralParams[collateralIndex]" */ calldata_array_index_access_struct_CollateralParams_calldata_dyn_calldata(expr_offset_3, expr_length_3, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(36)))
                        let _190 := shr(128, sload(/** @src 0:40655:40678  "_marketState.lossFactor" */ mload(0x02a0)))
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let _191 := shr(128, sload(/** @src 0:40692:40724  "_marketState.continuousFeeCredit" */ add(mload(0x02a0), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 1)))
                        /// @src 0:40357:40734  "EventsLib.Liquidate(..."
                        let _192 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                        mstore(_192, /** @src 0:40390:40400  "msg.sender" */ caller())
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(/** @src 7:792:802  "60 minutes" */ add(_192, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32), mload(0x0280))
                        mstore(/** @src 7:792:802  "60 minutes" */ add(_192, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 64), mload(0x0260))
                        mstore(/** @src 7:792:802  "60 minutes" */ add(_192, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 96), iszero(iszero(value_34)))
                        mstore(/** @src 7:792:802  "60 minutes" */ add(_192, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 128), and(value_35, 0xffffffffffffffffffffffffffffffffffffffff))
                        mstore(/** @src 7:792:802  "60 minutes" */ add(_192, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 160), and(expr_65, 0xffffffffffffffffffffffffffffffffffffffff))
                        mstore(/** @src 7:792:802  "60 minutes" */ add(_192, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 192), var_badDebt)
                        mstore(/** @src 7:792:802  "60 minutes" */ add(_192, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 224), _190)
                        mstore(/** @src 7:792:802  "60 minutes" */ add(_192, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 256), _191)
                        /// @src 0:40357:40734  "EventsLib.Liquidate(..."
                        log4(_192, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 288, /** @src 0:40357:40734  "EventsLib.Liquidate(..." */ 0xb137b989b9fd54b984273db8f16364f52f383aaca56076a320c1896e9fc2dad9, mload(0x0300), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:40357:40734  "EventsLib.Liquidate(..." */ expr_66, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff), and(value4_2, 0xffffffffffffffffffffffffffffffffffffffff))
                        /// @src 0:40774:40797  "market.collateralParams"
                        let expr_offset_4, expr_length_4 := access_calldata_tail_array_struct_CollateralParams_calldata_dyn_calldata(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ add(4, calldataload(4)), /** @src 0:36525:36548  "market.collateralParams" */ add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(4), 100))
                        /// @src 0:40832:40844  "seizedAssets"
                        fun_safeTransfer(/** @src 0:40774:40820  "market.collateralParams[collateralIndex].token" */ read_from_calldatat_address(/** @src 0:40774:40814  "market.collateralParams[collateralIndex]" */ calldata_array_index_access_struct_CollateralParams_calldata_dyn_calldata(expr_offset_4, expr_length_4, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(36))), /** @src 0:40832:40844  "seizedAssets" */ value_35, mload(0x0280))
                        /// @src 0:40856:41447  "if (callback != address(0)) {..."
                        if /** @src 0:40295:40317  "callback != address(0)" */ iszero(iszero(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(mload(0x02e0), 0xffffffffffffffffffffffffffffffffffffffff)))
                        /// @src 0:40856:41447  "if (callback != address(0)) {..."
                        {
                            /// @src 0:40923:41349  "ILiquidateCallback(callback)..."
                            let _193 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                            /// @src 0:40923:41349  "ILiquidateCallback(callback)..."
                            mstore(_193, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(225, 0x40724f01))
                            mstore(/** @src 0:40923:41349  "ILiquidateCallback(callback)..." */ add(_193, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 4), /** @src 0:40390:40400  "msg.sender" */ caller())
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            mstore(/** @src 7:792:802  "60 minutes" */ add(/** @src 0:40923:41349  "ILiquidateCallback(callback)..." */ _193, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 36), mload(0x0300))
                            /// @src 7:792:802  "60 minutes"
                            mstore(add(/** @src 0:40923:41349  "ILiquidateCallback(callback)..." */ _193, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 68), /** @src 7:792:802  "60 minutes" */ 320)
                            let tail_16 := add(/** @src 0:40923:41349  "ILiquidateCallback(callback)..." */ _193, /** @src 7:792:802  "60 minutes" */ 580)
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            mstore(/** @src 7:792:802  "60 minutes" */ add(/** @src 0:40923:41349  "ILiquidateCallback(callback)..." */ _193, /** @src 7:792:802  "60 minutes" */ 324), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(add(4, calldataload(4))))
                            mstore(/** @src 7:792:802  "60 minutes" */ add(/** @src 0:40923:41349  "ILiquidateCallback(callback)..." */ _193, /** @src 7:792:802  "60 minutes" */ 356), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(abi_decode_address(/** @src 7:792:802  "60 minutes" */ add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(4), 36)), 0xffffffffffffffffffffffffffffffffffffffff))
                            mstore(/** @src 7:792:802  "60 minutes" */ add(/** @src 0:40923:41349  "ILiquidateCallback(callback)..." */ _193, /** @src 7:792:802  "60 minutes" */ 388), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(abi_decode_address(/** @src 7:792:802  "60 minutes" */ add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(4), 68)), 0xffffffffffffffffffffffffffffffffffffffff))
                            /// @src 7:792:802  "60 minutes"
                            let rel_offset_of_tail := calldataload(/** @src 0:36525:36548  "market.collateralParams" */ add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(4), 100))
                            /// @src 7:792:802  "60 minutes"
                            if iszero(slt(rel_offset_of_tail, add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ sub(calldatasize(), calldataload(4)), /** @src 7:792:802  "60 minutes" */ not(34))))
                            {
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                revert(mload(0x0320), mload(0x0320))
                            }
                            /// @src 7:792:802  "60 minutes"
                            let _194 := add(rel_offset_of_tail, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(4))
                            /// @src 7:792:802  "60 minutes"
                            let value_39 := add(_194, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 36)
                            /// @src 7:792:802  "60 minutes"
                            if gt(calldataload(add(_194, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 4)), 0xffffffffffffffff)
                            /// @src 7:792:802  "60 minutes"
                            {
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                revert(mload(0x0320), mload(0x0320))
                            }
                            /// @src 7:792:802  "60 minutes"
                            if sgt(value_39, sub(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldatasize(), /** @src 7:792:802  "60 minutes" */ shl(7, calldataload(add(_194, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 4)))))
                            /// @src 7:792:802  "60 minutes"
                            {
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                revert(mload(0x0320), mload(0x0320))
                            }
                            /// @src 7:792:802  "60 minutes"
                            mstore(add(/** @src 0:40923:41349  "ILiquidateCallback(callback)..." */ _193, /** @src 7:792:802  "60 minutes" */ 420), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 256)
                            /// @src 7:792:802  "60 minutes"
                            let pos_11 := tail_16
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            mstore(tail_16, /** @src 7:792:802  "60 minutes" */ calldataload(add(_194, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 4)))
                            /// @src 7:792:802  "60 minutes"
                            pos_11 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ add(/** @src 0:40923:41349  "ILiquidateCallback(callback)..." */ _193, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 612)
                            /// @src 7:792:802  "60 minutes"
                            let srcPtr_1 := value_39
                            let i_1 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x0320)
                            /// @src 7:792:802  "60 minutes"
                            for { }
                            lt(i_1, calldataload(add(_194, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 4)))
                            /// @src 7:792:802  "60 minutes"
                            {
                                i_1 := add(i_1, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 1)
                            }
                            /// @src 7:792:802  "60 minutes"
                            {
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                mstore(pos_11, and(abi_decode_address(/** @src 7:792:802  "60 minutes" */ srcPtr_1), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                                mstore(/** @src 7:792:802  "60 minutes" */ add(pos_11, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32), calldataload(/** @src 7:792:802  "60 minutes" */ add(srcPtr_1, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32)))
                                mstore(/** @src 7:792:802  "60 minutes" */ add(pos_11, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 64), calldataload(/** @src 7:792:802  "60 minutes" */ add(srcPtr_1, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 64)))
                                mstore(/** @src 7:792:802  "60 minutes" */ add(pos_11, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 96), and(abi_decode_address(/** @src 7:792:802  "60 minutes" */ add(srcPtr_1, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 96)), 0xffffffffffffffffffffffffffffffffffffffff))
                                /// @src 7:792:802  "60 minutes"
                                pos_11 := add(pos_11, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 128)
                                /// @src 7:792:802  "60 minutes"
                                srcPtr_1 := add(srcPtr_1, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 128)
                            }
                            mstore(/** @src 7:792:802  "60 minutes" */ add(/** @src 0:40923:41349  "ILiquidateCallback(callback)..." */ _193, /** @src 7:792:802  "60 minutes" */ 452), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(/** @src 7:792:802  "60 minutes" */ add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(4), 132)))
                            mstore(/** @src 7:792:802  "60 minutes" */ add(/** @src 0:40923:41349  "ILiquidateCallback(callback)..." */ _193, /** @src 7:792:802  "60 minutes" */ 484), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(/** @src 7:792:802  "60 minutes" */ add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(4), 164)))
                            mstore(/** @src 7:792:802  "60 minutes" */ add(/** @src 0:40923:41349  "ILiquidateCallback(callback)..." */ _193, /** @src 7:792:802  "60 minutes" */ 516), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(abi_decode_address(/** @src 7:792:802  "60 minutes" */ add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(4), 196)), 0xffffffffffffffffffffffffffffffffffffffff))
                            mstore(/** @src 7:792:802  "60 minutes" */ add(/** @src 0:40923:41349  "ILiquidateCallback(callback)..." */ _193, /** @src 7:792:802  "60 minutes" */ 548), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(abi_decode_address(/** @src 0:35996:36017  "market.liquidatorGate" */ add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(4), 228)), 0xffffffffffffffffffffffffffffffffffffffff))
                            mstore(/** @src 7:792:802  "60 minutes" */ add(/** @src 0:40923:41349  "ILiquidateCallback(callback)..." */ _193, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 100), calldataload(36))
                            mstore(/** @src 7:792:802  "60 minutes" */ add(/** @src 0:40923:41349  "ILiquidateCallback(callback)..." */ _193, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 132), mload(0x0280))
                            mstore(/** @src 7:792:802  "60 minutes" */ add(/** @src 0:40923:41349  "ILiquidateCallback(callback)..." */ _193, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 164), mload(0x0260))
                            mstore(/** @src 7:792:802  "60 minutes" */ add(/** @src 0:40923:41349  "ILiquidateCallback(callback)..." */ _193, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 196), and(value4_2, 0xffffffffffffffffffffffffffffffffffffffff))
                            mstore(/** @src 7:792:802  "60 minutes" */ add(/** @src 0:40923:41349  "ILiquidateCallback(callback)..." */ _193, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 228), and(value_35, 0xffffffffffffffffffffffffffffffffffffffff))
                            /// @src 7:792:802  "60 minutes"
                            mstore(add(/** @src 0:40923:41349  "ILiquidateCallback(callback)..." */ _193, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 260), /** @src 7:792:802  "60 minutes" */ add(sub(pos_11, /** @src 0:40923:41349  "ILiquidateCallback(callback)..." */ _193), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(3)))
                            /// @src 7:792:802  "60 minutes"
                            let tail_17 := abi_encode_bytes_calldata(value8, value9, pos_11)
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            mstore(/** @src 7:792:802  "60 minutes" */ add(/** @src 0:40923:41349  "ILiquidateCallback(callback)..." */ _193, /** @src 7:792:802  "60 minutes" */ 292), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ var_badDebt)
                            /// @src 0:40923:41349  "ILiquidateCallback(callback)..."
                            let _195 := call(gas(), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(mload(0x02e0), 0xffffffffffffffffffffffffffffffffffffffff), mload(0x0320), /** @src 0:40923:41349  "ILiquidateCallback(callback)..." */ _193, sub(tail_17, _193), _193, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32)
                            /// @src 0:40923:41349  "ILiquidateCallback(callback)..."
                            if iszero(_195)
                            {
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                let pos_12 := mload(64)
                                returndatacopy(pos_12, mload(0x0320), returndatasize())
                                revert(pos_12, returndatasize())
                            }
                            /// @src 0:40923:41349  "ILiquidateCallback(callback)..."
                            let expr_67 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x0320)
                            /// @src 0:40923:41349  "ILiquidateCallback(callback)..."
                            if _195
                            {
                                let _196 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32
                                /// @src 0:40923:41349  "ILiquidateCallback(callback)..."
                                if gt(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32, /** @src 0:40923:41349  "ILiquidateCallback(callback)..." */ returndatasize()) { _196 := returndatasize() }
                                finalize_allocation(_193, _196)
                                let value0_16 := /** @src -1:-1:-1 */ 0
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                if slt(sub(/** @src 0:40923:41349  "ILiquidateCallback(callback)..." */ add(_193, _196), _193), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32)
                                {
                                    revert(/** @src -1:-1:-1 */ 0, 0)
                                }
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                value0_16 := mload(/** @src 0:40923:41349  "ILiquidateCallback(callback)..." */ _193)
                                expr_67 := value0_16
                            }
                            /// @src 7:792:802  "60 minutes"
                            if iszero(/** @src 0:40923:41369  "ILiquidateCallback(callback)..." */ eq(expr_67, /** @src 7:1030:1074  "keccak256(\"morpho.midnight.callbackSuccess\")" */ 0x7f87788ea698181ea4d28d1576d0ba4fc92c0dbe5bf75b43692af2ce91dbaea2))
                            /// @src 7:792:802  "60 minutes"
                            {
                                mstore(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x0320), /** @src 7:792:802  "60 minutes" */ shl(224, 0x70b53d4b))
                                revert(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x0320), 4)
                            }
                        }
                        /// @src 0:41490:41506  "market.loanToken"
                        let expr_68 := read_from_calldatat_address(add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(4), 68))
                        /// @src 0:41530:41541  "repaidUnits"
                        fun_safeTransferFrom(expr_68, expr_65, /** @src 0:41523:41527  "this" */ address(), /** @src 0:41530:41541  "repaidUnits" */ mload(0x0260))
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let memPos_19 := mload(64)
                        mstore(memPos_19, mload(0x0280))
                        mstore(add(memPos_19, 32), mload(0x0260))
                        return(memPos_19, 64)
                    }
                    case 0x9f5f86ae {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), 32)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let value0_17 := abi_decode_address_44122()
                        let _197 := sload(/** @src 0:15523:15535  "configurator" */ 0x09)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        if iszero(/** @src 0:15509:15535  "msg.sender == configurator" */ eq(/** @src 0:15509:15519  "msg.sender" */ caller(), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(_197, 0xffffffffffffffffffffffffffffffffffffffff)))
                        {
                            mstore(mload(0x0320), shl(228, 0x033b71e1))
                            revert(mload(0x0320), 4)
                        }
                        let _198 := and(value0_17, 0xffffffffffffffffffffffffffffffffffffffff)
                        sstore(/** @src 0:15523:15535  "configurator" */ 0x09, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ or(and(_197, not(0xffffffffffffffffffffffffffffffffffffffff)), _198))
                        /// @src 0:15611:15653  "EventsLib.SetConfigurator(newConfigurator)"
                        log2(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x0320), mload(0x0320), /** @src 0:15611:15653  "EventsLib.SetConfigurator(newConfigurator)" */ 0x2b1b0bd62fb5aaaa9f056fbb48d8bcd9d51a528081fc381ab981ce5c0f0b3153, _198)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        return(mload(0x0320), mload(0x0320))
                    }
                    case 0xa121e2a9 {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), 160)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let offset_13 := calldataload(4)
                        if gt(offset_13, 0xffffffffffffffff)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let value0_18 := abi_decode_struct_Market(add(4, offset_13), calldatasize())
                        let value_40 := calldataload(36)
                        let value_41 := calldataload(68)
                        let value3_2 := abi_decode_address_44129()
                        let value4_3 := abi_decode_address_44141()
                        let _199 := and(/** @src 0:34011:34033  "onBehalf == msg.sender" */ value3_2, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff)
                        /// @src 0:34011:34071  "onBehalf == msg.sender || isAuthorized[onBehalf][msg.sender]"
                        let expr_69 := /** @src 0:34011:34033  "onBehalf == msg.sender" */ eq(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _199, /** @src 0:34023:34033  "msg.sender" */ caller())
                        /// @src 0:34011:34071  "onBehalf == msg.sender || isAuthorized[onBehalf][msg.sender]"
                        if iszero(expr_69)
                        {
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            mstore(mload(0x0320), _199)
                            mstore(32, /** @src 0:34037:34049  "isAuthorized" */ 0x03)
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let dataSlot_36 := keccak256(mload(0x0320), 64)
                            /// @src 0:34037:34071  "isAuthorized[onBehalf][msg.sender]"
                            let dataSlot_37 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:34023:34033  "msg.sender" */ caller(), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                            mstore(0x20, /** @src 0:34037:34059  "isAuthorized[onBehalf]" */ dataSlot_36)
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            dataSlot_37 := keccak256(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x40)
                            /// @src 0:34011:34071  "onBehalf == msg.sender || isAuthorized[onBehalf][msg.sender]"
                            expr_69 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(sload(/** @src 0:34037:34071  "isAuthorized[onBehalf][msg.sender]" */ dataSlot_37), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xff)
                        }
                        if iszero(expr_69)
                        {
                            mstore(mload(0x0320), shl(232, 8565801))
                            revert(mload(0x0320), 4)
                        }
                        /// @src 0:34111:34130  "touchMarket(market)"
                        let expr_70 := fun_touchMarket(value0_18)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let cleaned_72 := and(mload(/** @src 0:34166:34206  "market.collateralParams[collateralIndex]" */ mload(memory_array_index_access_struct_CollateralParams_dyn(/** @src 0:34166:34189  "market.collateralParams" */ mload(add(value0_18, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 96)), /** @src 0:34166:34206  "market.collateralParams[collateralIndex]" */ value_40))), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff)
                        mstore(mload(0x0320), expr_70)
                        mstore(32, mload(0x0320))
                        let dataSlot_38 := keccak256(mload(0x0320), 64)
                        /// @src 0:34252:34274  "position[id][onBehalf]"
                        let dataSlot_39 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _199)
                        mstore(0x20, /** @src 0:34252:34264  "position[id]" */ dataSlot_38)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        dataSlot_39 := keccak256(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x40)
                        /// @src 0:34308:34328  "_position.collateral"
                        let _200 := add(/** @src 0:34252:34274  "position[id][onBehalf]" */ dataSlot_39, /** @src 0:34308:34328  "_position.collateral" */ 3)
                        /// @src 0:34308:34345  "_position.collateral[collateralIndex]"
                        let _201, _202 := storage_array_index_access_uint128_(_200, value_40)
                        /// @src 0:34308:34354  "_position.collateral[collateralIndex] - assets"
                        let expr_71 := checked_sub_uint256(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(shr(shl(/** @src 0:34308:34328  "_position.collateral" */ 3, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _202), sload(/** @src 0:34308:34345  "_position.collateral[collateralIndex]" */ _201)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff), /** @src 0:34308:34354  "_position.collateral[collateralIndex] - assets" */ value_41)
                        /// @src 0:34404:34437  "UtilsLib.toUint128(newCollateral)"
                        let expr_72 := fun_toUint128(expr_71)
                        /// @src 0:34364:34401  "_position.collateral[collateralIndex]"
                        let _203, _204 := storage_array_index_access_uint128_(_200, value_40)
                        /// @src 0:34364:34437  "_position.collateral[collateralIndex] = UtilsLib.toUint128(newCollateral)"
                        update_storage_value_uint128_to_uint128(_203, _204, expr_72)
                        /// @src 0:34452:34484  "newCollateral == 0 && assets > 0"
                        let expr_73 := /** @src 0:34452:34470  "newCollateral == 0" */ iszero(expr_71)
                        /// @src 0:34452:34484  "newCollateral == 0 && assets > 0"
                        if expr_73
                        {
                            expr_73 := /** @src 0:34474:34484  "assets > 0" */ iszero(iszero(value_41))
                        }
                        /// @src 0:34448:34592  "if (newCollateral == 0 && assets > 0) {..."
                        if expr_73
                        {
                            /// @src 0:34529:34555  "_position.collateralBitmap"
                            let _205 := add(/** @src 0:34252:34274  "position[id][onBehalf]" */ dataSlot_39, /** @src 0:34529:34555  "_position.collateralBitmap" */ 2)
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let _206 := shr(128, sload(/** @src 0:34529:34555  "_position.collateralBitmap" */ _205))
                            /// @src 0:34529:34581  "_position.collateralBitmap.clearBit(collateralIndex)"
                            let var_7 := /** @src -1:-1:-1 */ 0
                            /// @src 12:2155:2191  "return uint128(bitmap & ~(1 << bit))"
                            var_7 := /** @src 12:2170:2190  "bitmap & ~(1 << bit)" */ and(and(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _206, /** @src 12:2179:2190  "~(1 << bit)" */ not(/** @src 7:892:894  "16" */ shl(/** @src 0:34529:34581  "_position.collateralBitmap.clearBit(collateralIndex)" */ value_40, /** @src 12:2181:2182  "1" */ 0x01))), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)
                            /// @src 0:34500:34581  "_position.collateralBitmap = _position.collateralBitmap.clearBit(collateralIndex)"
                            update_storage_value_offset_uint128_to_uint128(_205, /** @src 0:34529:34581  "_position.collateralBitmap.clearBit(collateralIndex)" */ var_7)
                        }
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        if iszero(/** @src 0:34610:34641  "isHealthy(market, id, onBehalf)" */ fun_isHealthy(value0_18, expr_70, value3_2))
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        {
                            mstore(mload(0x0320), shl(225, 0x27a7239f))
                            revert(mload(0x0320), 4)
                        }
                        /// @src 0:34679:34768  "EventsLib.WithdrawCollateral(msg.sender, id, collateralToken, assets, onBehalf, receiver)"
                        let _207 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                        mstore(_207, /** @src 0:34023:34033  "msg.sender" */ caller())
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(add(_207, 32), value_41)
                        mstore(add(_207, 64), and(value4_3, 0xffffffffffffffffffffffffffffffffffffffff))
                        /// @src 0:34679:34768  "EventsLib.WithdrawCollateral(msg.sender, id, collateralToken, assets, onBehalf, receiver)"
                        log4(_207, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 96, /** @src 0:34679:34768  "EventsLib.WithdrawCollateral(msg.sender, id, collateralToken, assets, onBehalf, receiver)" */ 0x626c0b2bb9d8e812f145a6a7bdb09fe8fb92c53781755f343d5fd65c7e27949a, expr_70, cleaned_72, _199)
                        /// @src 0:34835:34841  "assets"
                        fun_safeTransfer(cleaned_72, value4_3, value_41)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        return(mload(0x0320), mload(0x0320))
                    }
                    case 0xa3330aa3 {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), 32)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let offset_14 := calldataload(4)
                        if gt(offset_14, 0xffffffffffffffff)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let ret_4 := fun_touchMarket(abi_decode_struct_Market(add(4, offset_14), calldatasize()))
                        let memPos_20 := mload(64)
                        mstore(memPos_20, ret_4)
                        return(memPos_20, 32)
                    }
                    case 0xa6db1750 {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), 128)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let offset_15 := calldataload(4)
                        if gt(offset_15, 0xffffffffffffffff)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let value0_19 := abi_decode_struct_Market(add(4, offset_15), calldatasize())
                        let value_42 := calldataload(36)
                        let value2_4 := abi_decode_address_44128()
                        let value3_3 := abi_decode_address_44129()
                        let _208 := and(/** @src 0:30540:30562  "onBehalf == msg.sender" */ value2_4, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff)
                        /// @src 0:30540:30600  "onBehalf == msg.sender || isAuthorized[onBehalf][msg.sender]"
                        let expr_74 := /** @src 0:30540:30562  "onBehalf == msg.sender" */ eq(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _208, /** @src 0:30552:30562  "msg.sender" */ caller())
                        /// @src 0:30540:30600  "onBehalf == msg.sender || isAuthorized[onBehalf][msg.sender]"
                        if iszero(expr_74)
                        {
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            mstore(mload(0x0320), _208)
                            mstore(32, /** @src 0:30566:30578  "isAuthorized" */ 0x03)
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let dataSlot_40 := keccak256(mload(0x0320), 64)
                            /// @src 0:30566:30600  "isAuthorized[onBehalf][msg.sender]"
                            let dataSlot_41 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:30552:30562  "msg.sender" */ caller(), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                            mstore(0x20, /** @src 0:30566:30588  "isAuthorized[onBehalf]" */ dataSlot_40)
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            dataSlot_41 := keccak256(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x40)
                            /// @src 0:30540:30600  "onBehalf == msg.sender || isAuthorized[onBehalf][msg.sender]"
                            expr_74 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(sload(/** @src 0:30566:30600  "isAuthorized[onBehalf][msg.sender]" */ dataSlot_41), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xff)
                        }
                        if iszero(expr_74)
                        {
                            mstore(mload(0x0320), shl(232, 8565801))
                            revert(mload(0x0320), 4)
                        }
                        /// @src 0:30640:30659  "touchMarket(market)"
                        let expr_75 := fun_touchMarket(value0_19)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(mload(0x0320), expr_75)
                        mstore(32, 1)
                        let dataSlot_42 := keccak256(mload(0x0320), 64)
                        /// @src 0:30729:30766  "_updatePosition(market, id, onBehalf)"
                        let expr_component_9, expr_component_10, expr_component_11 := fun_updatePosition(value0_19, expr_75, value2_4)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(mload(0x0320), expr_75)
                        mstore(32, mload(0x0320))
                        let dataSlot_43 := keccak256(mload(0x0320), 64)
                        /// @src 0:30806:30828  "position[id][onBehalf]"
                        let dataSlot_44 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _208)
                        mstore(0x20, /** @src 0:30806:30818  "position[id]" */ dataSlot_43)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        dataSlot_44 := keccak256(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x40)
                        /// @src 0:30838:30864  "uint128 pendingFeeDecrease"
                        let var_pendingFeeDecrease := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x0320)
                        /// @src 0:30838:30864  "uint128 pendingFeeDecrease"
                        var_pendingFeeDecrease := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x0320)
                        let _209 := sload(/** @src 0:30806:30828  "position[id][onBehalf]" */ dataSlot_44)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let cleaned_73 := and(_209, 0xffffffffffffffffffffffffffffffff)
                        /// @src 0:30874:31076  "if (_position.credit > 0) {..."
                        if /** @src 0:30878:30898  "_position.credit > 0" */ iszero(iszero(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ cleaned_73))
                        /// @src 0:30874:31076  "if (_position.credit > 0) {..."
                        {
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let _210 := shr(128, _209)
                            /// @src 0:30914:31009  "pendingFeeDecrease = UtilsLib.toUint128(_position.pendingFee.mulDivUp(units, _position.credit))"
                            var_pendingFeeDecrease := /** @src 0:30935:31009  "UtilsLib.toUint128(_position.pendingFee.mulDivUp(units, _position.credit))" */ fun_toUint128(/** @src 0:30954:31008  "_position.pendingFee.mulDivUp(units, _position.credit)" */ fun_mulDivUp(_210, value_42, cleaned_73))
                            /// @src 0:31023:31065  "_position.pendingFee -= pendingFeeDecrease"
                            update_storage_value_offset_uint128_to_uint128(/** @src 0:30806:30828  "position[id][onBehalf]" */ dataSlot_44, /** @src 0:31023:31065  "_position.pendingFee -= pendingFeeDecrease" */ checked_sub_uint128(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _210, /** @src 0:31023:31065  "_position.pendingFee -= pendingFeeDecrease" */ var_pendingFeeDecrease))
                        }
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        sstore(/** @src 0:30806:30828  "position[id][onBehalf]" */ dataSlot_44, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ or(and(sload(/** @src 0:30806:30828  "position[id][onBehalf]" */ dataSlot_44), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(0xffffffffffffffffffffffffffffffff)), and(/** @src 0:31085:31130  "_position.credit -= UtilsLib.toUint128(units)" */ checked_sub_uint128(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(sload(/** @src 0:30806:30828  "position[id][onBehalf]" */ dataSlot_44), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff), /** @src 0:31105:31130  "UtilsLib.toUint128(units)" */ fun_toUint128(value_42)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)))
                        /// @src 0:31169:31194  "UtilsLib.toUint128(units)"
                        let expr_76 := fun_toUint128(value_42)
                        /// @src 0:31140:31165  "_marketState.withdrawable"
                        let _211 := add(dataSlot_42, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 1)
                        sstore(/** @src 0:31140:31194  "_marketState.withdrawable -= UtilsLib.toUint128(units)" */ _211, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ or(and(sload(/** @src 0:31140:31194  "_marketState.withdrawable -= UtilsLib.toUint128(units)" */ _211), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(0xffffffffffffffffffffffffffffffff)), and(/** @src 0:31140:31194  "_marketState.withdrawable -= UtilsLib.toUint128(units)" */ checked_sub_uint128(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(sload(/** @src 0:31140:31194  "_marketState.withdrawable -= UtilsLib.toUint128(units)" */ _211), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff), /** @src 0:31140:31194  "_marketState.withdrawable -= UtilsLib.toUint128(units)" */ expr_76), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)))
                        sstore(/** @src 0:31204:31256  "_marketState.totalUnits -= UtilsLib.toUint128(units)" */ dataSlot_42, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ or(and(sload(/** @src 0:31204:31256  "_marketState.totalUnits -= UtilsLib.toUint128(units)" */ dataSlot_42), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(0xffffffffffffffffffffffffffffffff)), and(/** @src 0:31204:31256  "_marketState.totalUnits -= UtilsLib.toUint128(units)" */ checked_sub_uint128(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(sload(/** @src 0:31204:31256  "_marketState.totalUnits -= UtilsLib.toUint128(units)" */ dataSlot_42), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff), /** @src 0:31231:31256  "UtilsLib.toUint128(units)" */ fun_toUint128(value_42)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)))
                        /// @src 0:31272:31353  "EventsLib.Withdraw(msg.sender, id, units, onBehalf, receiver, pendingFeeDecrease)"
                        let _212 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                        mstore(_212, /** @src 0:30552:30562  "msg.sender" */ caller())
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(add(_212, 32), value_42)
                        mstore(add(_212, 64), and(var_pendingFeeDecrease, 0xffffffffffffffffffffffffffffffff))
                        /// @src 0:31272:31353  "EventsLib.Withdraw(msg.sender, id, units, onBehalf, receiver, pendingFeeDecrease)"
                        log4(_212, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 96, /** @src 0:31272:31353  "EventsLib.Withdraw(msg.sender, id, units, onBehalf, receiver, pendingFeeDecrease)" */ 0x7a5e8e1731f88cf0c25f88fc7d5618e481e87be4d83f614e601850c2ff082fd7, expr_75, _208, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:31272:31353  "EventsLib.Withdraw(msg.sender, id, units, onBehalf, receiver, pendingFeeDecrease)" */ value3_3, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                        /// @src 0:31421:31426  "units"
                        fun_safeTransfer(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(mload(/** @src 0:31393:31409  "market.loanToken" */ add(value0_19, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 64)), 0xffffffffffffffffffffffffffffffffffffffff), /** @src 0:31421:31426  "units" */ value3_3, value_42)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        return(mload(0x0320), mload(0x0320))
                    }
                    case 0xa9bef809 {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let param_5, param_6 := abi_decode_bytes32t_uint256(calldatasize())
                        let ret_5 := fun_settlementFee(param_5, param_6)
                        let memPos_21 := mload(64)
                        mstore(memPos_21, ret_5)
                        return(memPos_21, 32)
                    }
                    case 0xac9650d8 {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), 32)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let offset_16 := calldataload(4)
                        if gt(offset_16, 0xffffffffffffffff)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let value0_20, value1_6 := abi_decode_array_address_dyn_calldata(add(4, offset_16), calldatasize())
                        /// @src 0:15078:15091  "uint256 i = 0"
                        let var_i_2 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x0320)
                        let _213 := add(sub(calldatasize(), value0_20), not(30))
                        /// @src 0:15073:15391  "for (uint256 i = 0; i < calls.length; i++) {..."
                        for { }
                        /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 1
                        /// @src 0:15078:15091  "uint256 i = 0"
                        {
                            /// @src 0:15111:15114  "i++"
                            var_i_2 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ add(/** @src 0:15111:15114  "i++" */ var_i_2, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 1)
                        }
                        /// @src 0:15111:15114  "i++"
                        {
                            /// @src 0:15093:15109  "i < calls.length"
                            let _214 := iszero(lt(var_i_2, /** @src 0:15097:15109  "calls.length" */ value1_6))
                            /// @src 0:15093:15109  "i < calls.length"
                            if _214 { break }
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            _214 := /** @src -1:-1:-1 */ mload(0x0320)
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let rel_offset_of_tail_1 := calldataload(add(value0_20, shl(5, var_i_2)))
                            if iszero(slt(rel_offset_of_tail_1, _213))
                            {
                                revert(mload(0x0320), mload(0x0320))
                            }
                            let addr := add(value0_20, rel_offset_of_tail_1)
                            let length := calldataload(addr)
                            if gt(length, 0xffffffffffffffff)
                            {
                                revert(mload(0x0320), mload(0x0320))
                            }
                            let addr_1 := add(addr, 32)
                            if sgt(addr_1, sub(calldatasize(), length))
                            {
                                revert(mload(0x0320), mload(0x0320))
                            }
                            /// @src 0:15172:15208  "address(this).delegatecall(calls[i])"
                            let _215 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                            calldatacopy(_215, addr_1, length)
                            let _216 := add(_215, length)
                            mstore(_216, mload(0x0320))
                            /// @src 0:15172:15208  "address(this).delegatecall(calls[i])"
                            let expr_component_12 := delegatecall(gas(), /** @src 0:15180:15184  "this" */ address(), /** @src 0:15172:15208  "address(this).delegatecall(calls[i])" */ _215, sub(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _216, /** @src 0:15172:15208  "address(this).delegatecall(calls[i])" */ _215), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x0320), mload(0x0320))
                            /// @src 0:15172:15208  "address(this).delegatecall(calls[i])"
                            let expr_component_mpos := extract_returndata()
                            /// @src 0:15222:15381  "if (!success) {..."
                            if /** @src 0:15226:15234  "!success" */ iszero(expr_component_12)
                            /// @src 0:15222:15381  "if (!success) {..."
                            {
                                /// @src 0:15254:15367  "assembly (\"memory-safe\") {..."
                                revert(add(expr_component_mpos, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32), /** @src 0:15254:15367  "assembly (\"memory-safe\") {..." */ mload(expr_component_mpos))
                            }
                        }
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        return(mload(0x0320), mload(0x0320))
                    }
                    case 0xb19805af {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), 32)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let value0_21 := abi_decode_address_44122()
                        if iszero(/** @src 0:15737:15763  "msg.sender == configurator" */ eq(/** @src 0:15737:15747  "msg.sender" */ caller(), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(sload(/** @src 0:15751:15763  "configurator" */ 0x09), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff)))
                        {
                            mstore(mload(0x0320), shl(228, 0x033b71e1))
                            revert(mload(0x0320), 4)
                        }
                        let _217 := and(value0_21, 0xffffffffffffffffffffffffffffffffffffffff)
                        sstore(/** @src 0:15794:15818  "feeSetter = newFeeSetter" */ 0x0a, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ or(and(sload(/** @src 0:15794:15818  "feeSetter = newFeeSetter" */ 0x0a), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(0xffffffffffffffffffffffffffffffffffffffff)), _217))
                        /// @src 0:15833:15869  "EventsLib.SetFeeSetter(newFeeSetter)"
                        log2(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x0320), mload(0x0320), /** @src 0:15833:15869  "EventsLib.SetFeeSetter(newFeeSetter)" */ 0x9993507f53024702e2de1be66f6c48c8957ac708927b86b3bdf4e335f5869470, _217)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        return(mload(0x0320), mload(0x0320))
                    }
                    case 0xb485f3b8 {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), 32)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        mstore(mload(0x0320), calldataload(4))
                        mstore(32, /** @src 0:14582:14632  "mapping(uint256 lltv => bool) public isLltvEnabled" */ 7)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let value_43 := and(sload(keccak256(mload(0x0320), 64)), 0xff)
                        let memPos_22 := mload(64)
                        mstore(memPos_22, iszero(iszero(value_43)))
                        return(memPos_22, 32)
                    }
                    case 0xb502e1f9 {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), 64)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let value1_7 := abi_decode_address_44120()
                        mstore(mload(0x0320), calldataload(4))
                        mstore(32, mload(0x0320))
                        let dataSlot_45 := keccak256(mload(0x0320), 64)
                        /// @src 0:52766:52784  "position[id][user]"
                        let dataSlot_46 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:52766:52784  "position[id][user]" */ value1_7, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                        mstore(0x20, /** @src 0:52766:52778  "position[id]" */ dataSlot_45)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        dataSlot_46 := keccak256(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x40)
                        let _218 := shr(128, sload(/** @src 0:52766:52801  "position[id][user].collateralBitmap" */ add(/** @src 0:52766:52784  "position[id][user]" */ dataSlot_46, /** @src 0:52766:52801  "position[id][user].collateralBitmap" */ 2)))
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let memPos_23 := mload(64)
                        mstore(memPos_23, _218)
                        return(memPos_23, 32)
                    }
                    case 0xb78212ab {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), 96)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let value0_22 := abi_decode_address_44122()
                        let value_44 := /** @src -1:-1:-1 */ mload(0x0320)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        value_44 := calldataload(36)
                        let _219 := iszero(iszero(value_44))
                        if iszero(eq(value_44, _219))
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let _220 := and(abi_decode_address_44128(), 0xffffffffffffffffffffffffffffffffffffffff)
                        /// @src 0:42136:42196  "onBehalf == msg.sender || isAuthorized[onBehalf][msg.sender]"
                        let expr_77 := /** @src 0:42136:42158  "onBehalf == msg.sender" */ eq(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _220, /** @src 0:42148:42158  "msg.sender" */ caller())
                        /// @src 0:42136:42196  "onBehalf == msg.sender || isAuthorized[onBehalf][msg.sender]"
                        if iszero(expr_77)
                        {
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            mstore(mload(0x0320), _220)
                            mstore(32, /** @src 0:42162:42174  "isAuthorized" */ 0x03)
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let dataSlot_47 := keccak256(mload(0x0320), 64)
                            /// @src 0:42162:42196  "isAuthorized[onBehalf][msg.sender]"
                            let dataSlot_48 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:42148:42158  "msg.sender" */ caller(), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                            mstore(0x20, /** @src 0:42162:42184  "isAuthorized[onBehalf]" */ dataSlot_47)
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            dataSlot_48 := keccak256(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x40)
                            /// @src 0:42136:42196  "onBehalf == msg.sender || isAuthorized[onBehalf][msg.sender]"
                            expr_77 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(sload(/** @src 0:42162:42196  "isAuthorized[onBehalf][msg.sender]" */ dataSlot_48), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xff)
                        }
                        if iszero(expr_77)
                        {
                            mstore(mload(0x0320), shl(232, 8565801))
                            revert(mload(0x0320), 4)
                        }
                        mstore(mload(0x0320), _220)
                        mstore(32, /** @src 0:42223:42235  "isAuthorized" */ 0x03)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let dataSlot_49 := keccak256(mload(0x0320), 64)
                        /// @src 0:42223:42257  "isAuthorized[onBehalf][authorized]"
                        let dataSlot_50 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:42223:42257  "isAuthorized[onBehalf][authorized]" */ value0_22, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                        mstore(0x20, /** @src 0:42223:42245  "isAuthorized[onBehalf]" */ dataSlot_49)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        dataSlot_50 := keccak256(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x40)
                        /// @src 7:190:194  "1e18"
                        let value_45 := and(sload(/** @src 0:42223:42257  "isAuthorized[onBehalf][authorized]" */ dataSlot_50), /** @src 7:190:194  "1e18" */ not(255))
                        sstore(/** @src 0:42223:42257  "isAuthorized[onBehalf][authorized]" */ dataSlot_50, /** @src 7:190:194  "1e18" */ or(value_45, and(_219, 255)))
                        /// @src 0:42290:42366  "EventsLib.SetIsAuthorized(msg.sender, authorized, newIsAuthorized, onBehalf)"
                        let _221 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                        mstore(_221, _219)
                        /// @src 0:42290:42366  "EventsLib.SetIsAuthorized(msg.sender, authorized, newIsAuthorized, onBehalf)"
                        log4(_221, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32, /** @src 0:42290:42366  "EventsLib.SetIsAuthorized(msg.sender, authorized, newIsAuthorized, onBehalf)" */ 0x50b9eb33249282f66c7ee7f45c0e4f22a839f9b8026310efa855ee7abab13827, /** @src 0:42148:42158  "msg.sender" */ caller(), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:42290:42366  "EventsLib.SetIsAuthorized(msg.sender, authorized, newIsAuthorized, onBehalf)" */ value0_22, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff), /** @src 0:42290:42366  "EventsLib.SetIsAuthorized(msg.sender, authorized, newIsAuthorized, onBehalf)" */ _220)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        return(mload(0x0320), mload(0x0320))
                    }
                    case 0xc04e7898 {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), 32)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        mstore(mload(0x0320), calldataload(4))
                        mstore(32, 1)
                        let value_46 := and(shr(112, sload(/** @src 0:54213:54242  "marketState[id].continuousFee" */ add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ keccak256(mload(0x0320), 64), /** @src 0:54213:54242  "marketState[id].continuousFee" */ 2))), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffff)
                        let memPos_24 := mload(64)
                        mstore(memPos_24, value_46)
                        return(memPos_24, 32)
                    }
                    case 0xc18f47da {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), 64)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let value0_23 := abi_decode_address_44122()
                        let value_47 := calldataload(36)
                        mstore(mload(0x0320), and(value0_23, 0xffffffffffffffffffffffffffffffffffffffff))
                        mstore(32, 4)
                        let dataSlot_51 := keccak256(mload(0x0320), 64)
                        /// @src 0:14367:14437  "mapping(address loanToken => uint16[7]) public defaultSettlementFeeCbp"
                        if iszero(lt(value_47, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x07))
                        /// @src 0:14367:14437  "mapping(address loanToken => uint16[7]) public defaultSettlementFeeCbp"
                        {
                            revert(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x0320), mload(0x0320))
                        }
                        /// @src 0:14367:14437  "mapping(address loanToken => uint16[7]) public defaultSettlementFeeCbp"
                        let slot, offset_17 := storage_array_index_access_uint(dataSlot_51, value_47)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let value_48 := and(shr(shl(3, offset_17), sload(/** @src 0:14367:14437  "mapping(address loanToken => uint16[7]) public defaultSettlementFeeCbp" */ slot)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffff)
                        let memPos_25 := mload(64)
                        mstore(memPos_25, value_48)
                        return(memPos_25, 32)
                    }
                    case 0xc3accd48 {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), 32)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let value0_24 := abi_decode_address_44122()
                        if iszero(/** @src 0:15955:15981  "msg.sender == configurator" */ eq(/** @src 0:15955:15965  "msg.sender" */ caller(), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(sload(/** @src 0:15969:15981  "configurator" */ 0x09), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff)))
                        {
                            mstore(mload(0x0320), shl(228, 0x033b71e1))
                            revert(mload(0x0320), 4)
                        }
                        let _222 := and(value0_24, 0xffffffffffffffffffffffffffffffffffffffff)
                        sstore(/** @src 0:16012:16038  "feeClaimer = newFeeClaimer" */ 0x0b, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ or(and(sload(/** @src 0:16012:16038  "feeClaimer = newFeeClaimer" */ 0x0b), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(0xffffffffffffffffffffffffffffffffffffffff)), _222))
                        /// @src 0:16053:16091  "EventsLib.SetFeeClaimer(newFeeClaimer)"
                        log2(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x0320), mload(0x0320), /** @src 0:16053:16091  "EventsLib.SetFeeClaimer(newFeeClaimer)" */ 0x95fa75db724442e818e27072c0420043307335fb3e4913b4c371e70cd902c2e2, _222)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        return(mload(0x0320), mload(0x0320))
                    }
                    case 0xc60c6271 {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), 64)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let value1_8 := abi_decode_address_44120()
                        mstore(mload(0x0320), calldataload(4))
                        mstore(32, mload(0x0320))
                        let dataSlot_52 := keccak256(mload(0x0320), 64)
                        /// @src 0:52214:52232  "position[id][user]"
                        let dataSlot_53 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(value1_8, 0xffffffffffffffffffffffffffffffffffffffff))
                        mstore(0x20, /** @src 0:52214:52226  "position[id]" */ dataSlot_52)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        dataSlot_53 := keccak256(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x40)
                        let _223 := shr(128, sload(/** @src 0:52214:52232  "position[id][user]" */ dataSlot_53))
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let memPos_26 := mload(64)
                        mstore(memPos_26, _223)
                        return(memPos_26, 32)
                    }
                    case 0xca286bb9 {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), 64)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let value1_9 := abi_decode_address_44120()
                        mstore(mload(0x0320), calldataload(4))
                        mstore(32, mload(0x0320))
                        let dataSlot_54 := keccak256(mload(0x0320), 64)
                        /// @src 0:52081:52099  "position[id][user]"
                        let dataSlot_55 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(value1_9, 0xffffffffffffffffffffffffffffffffffffffff))
                        mstore(0x20, /** @src 0:52081:52093  "position[id]" */ dataSlot_54)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        dataSlot_55 := keccak256(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x40)
                        let cleaned_74 := and(sload(/** @src 0:52081:52099  "position[id][user]" */ dataSlot_55), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)
                        let memPos_27 := mload(64)
                        mstore(memPos_27, cleaned_74)
                        return(memPos_27, 32)
                    }
                    case 0xd4de4974 {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let param_7, param_8, param_9 := abi_decode_struct_Markett_bytes32t_address(calldatasize())
                        let ret_6, ret_7, ret_8 := fun_updatePositionView(param_7, param_8, param_9)
                        let memPos_28 := mload(64)
                        return(memPos_28, sub(abi_encode_uint128_uint128_uint128(memPos_28, ret_6, ret_7, ret_8), memPos_28))
                    }
                    case 0xdb94c029 {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), 32)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        mstore(mload(0x0320), calldataload(4))
                        mstore(32, 1)
                        let value_49 := and(shr(144, sload(/** @src 0:54335:54362  "marketState[id].tickSpacing" */ add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ keccak256(mload(0x0320), 64), /** @src 0:54335:54362  "marketState[id].tickSpacing" */ 2))), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xff)
                        let memPos_29 := mload(64)
                        mstore(memPos_29, value_49)
                        return(memPos_29, 32)
                    }
                    case 0xe20e9a64 {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), 64)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let value1_10 := abi_decode_address_44120()
                        mstore(mload(0x0320), calldataload(4))
                        mstore(32, mload(0x0320))
                        let dataSlot_56 := keccak256(mload(0x0320), 64)
                        /// @src 0:52497:52515  "position[id][user]"
                        let dataSlot_57 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:52497:52515  "position[id][user]" */ value1_10, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                        mstore(0x20, /** @src 0:52497:52509  "position[id]" */ dataSlot_56)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        dataSlot_57 := keccak256(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x40)
                        let _224 := shr(128, sload(/** @src 0:52497:52527  "position[id][user].lastAccrual" */ add(/** @src 0:52497:52515  "position[id][user]" */ dataSlot_57, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 1)))
                        let memPos_30 := mload(64)
                        mstore(memPos_30, _224)
                        return(memPos_30, 32)
                    }
                    case 0xe29dfba8 {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), 64)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        mstore(mload(0x0320), and(abi_decode_address_44122(), 0xffffffffffffffffffffffffffffffffffffffff))
                        mstore(32, /** @src 0:14195:14269  "mapping(address user => mapping(bytes32 group => uint128)) public consumed" */ 2)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let dataSlot_58 := keccak256(mload(0x0320), 64)
                        mstore(mload(0x0320), calldataload(36))
                        mstore(32, dataSlot_58)
                        let value_50 := and(sload(keccak256(mload(0x0320), 64)), 0xffffffffffffffffffffffffffffffff)
                        let memPos_31 := mload(64)
                        mstore(memPos_31, value_50)
                        return(memPos_31, 32)
                    }
                    case 0xead29b0b {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), 32)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        mstore(mload(0x0320), calldataload(4))
                        mstore(32, 1)
                        let dataSlot_59 := keccak256(mload(0x0320), 64)
                        let _225 := sload(/** @src 0:14136:14189  "mapping(bytes32 id => MarketState) public marketState" */ dataSlot_59)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let _226 := sload(/** @src 0:14136:14189  "mapping(bytes32 id => MarketState) public marketState" */ add(dataSlot_59, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 1))
                        let _227 := sload(/** @src 0:14136:14189  "mapping(bytes32 id => MarketState) public marketState" */ add(dataSlot_59, 2))
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let memPos_32 := mload(64)
                        mstore(memPos_32, and(_225, 0xffffffffffffffffffffffffffffffff))
                        mstore(add(memPos_32, 32), shr(128, _225))
                        mstore(add(memPos_32, 64), and(_226, 0xffffffffffffffffffffffffffffffff))
                        mstore(add(memPos_32, 96), shr(128, _226))
                        mstore(add(memPos_32, 128), and(_227, 0xffff))
                        mstore(add(memPos_32, 160), and(shr(16, _227), 0xffff))
                        mstore(add(memPos_32, 192), and(shr(32, _227), 0xffff))
                        mstore(add(memPos_32, 224), and(shr(48, _227), 0xffff))
                        mstore(add(memPos_32, 256), and(shr(64, _227), 0xffff))
                        mstore(add(memPos_32, 288), and(shr(80, _227), 0xffff))
                        mstore(add(memPos_32, 320), and(shr(96, _227), 0xffff))
                        mstore(add(memPos_32, 352), and(shr(112, _227), 0xffffffff))
                        mstore(add(memPos_32, 384), and(shr(144, _227), 0xff))
                        return(memPos_32, 416)
                    }
                    case 0xecdcc72d {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), 96)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let value1_11 := abi_decode_address_44120()
                        mstore(mload(0x0320), calldataload(4))
                        mstore(32, mload(0x0320))
                        let dataSlot_60 := keccak256(mload(0x0320), 64)
                        /// @src 0:52924:52942  "position[id][user]"
                        let dataSlot_61 := /** @src -1:-1:-1 */ 0
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:52924:52942  "position[id][user]" */ value1_11, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                        mstore(0x20, /** @src 0:52924:52936  "position[id]" */ dataSlot_60)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        dataSlot_61 := keccak256(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x40)
                        /// @src 0:52924:52960  "position[id][user].collateral[index]"
                        let _228, _229 := storage_array_index_access_uint128_(/** @src 0:52924:52953  "position[id][user].collateral" */ add(/** @src 0:52924:52942  "position[id][user]" */ dataSlot_61, /** @src 0:52924:52953  "position[id][user].collateral" */ 3), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ calldataload(68))
                        let value_51 := and(shr(shl(/** @src 0:52924:52953  "position[id][user].collateral" */ 3, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _229), sload(/** @src 0:52924:52960  "position[id][user].collateral[index]" */ _228)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)
                        let memPos_33 := mload(64)
                        mstore(memPos_33, value_51)
                        return(memPos_33, 32)
                    }
                    case 0xf01fc06c {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), 96)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let value_52 := calldataload(4)
                        let value_53 := /** @src -1:-1:-1 */ mload(0x0320)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        value_53 := calldataload(36)
                        let _230 := and(value_53, 0xffffffffffffffffffffffffffffffff)
                        if iszero(eq(value_53, _230))
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let _231 := and(abi_decode_address_44128(), 0xffffffffffffffffffffffffffffffffffffffff)
                        /// @src 0:41697:41757  "onBehalf == msg.sender || isAuthorized[onBehalf][msg.sender]"
                        let expr_78 := /** @src 0:41697:41719  "onBehalf == msg.sender" */ eq(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _231, /** @src 0:41709:41719  "msg.sender" */ caller())
                        /// @src 0:41697:41757  "onBehalf == msg.sender || isAuthorized[onBehalf][msg.sender]"
                        if iszero(expr_78)
                        {
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            mstore(mload(0x0320), _231)
                            mstore(32, /** @src 0:41723:41735  "isAuthorized" */ 0x03)
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let dataSlot_62 := keccak256(mload(0x0320), 64)
                            /// @src 0:41723:41757  "isAuthorized[onBehalf][msg.sender]"
                            let dataSlot_63 := /** @src -1:-1:-1 */ 0
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:41709:41719  "msg.sender" */ caller(), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                            mstore(0x20, /** @src 0:41723:41745  "isAuthorized[onBehalf]" */ dataSlot_62)
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            dataSlot_63 := keccak256(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x40)
                            /// @src 0:41697:41757  "onBehalf == msg.sender || isAuthorized[onBehalf][msg.sender]"
                            expr_78 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(sload(/** @src 0:41723:41757  "isAuthorized[onBehalf][msg.sender]" */ dataSlot_63), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xff)
                        }
                        if iszero(expr_78)
                        {
                            mstore(mload(0x0320), shl(232, 8565801))
                            revert(mload(0x0320), 4)
                        }
                        mstore(mload(0x0320), _231)
                        mstore(32, /** @src 0:41802:41810  "consumed" */ 0x02)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let dataSlot_64 := keccak256(mload(0x0320), 64)
                        mstore(mload(0x0320), value_52)
                        mstore(32, dataSlot_64)
                        if /** @src 0:41792:41827  "amount >= consumed[onBehalf][group]" */ lt(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _230, and(sload(keccak256(mload(0x0320), 64)), 0xffffffffffffffffffffffffffffffff))
                        {
                            mstore(mload(0x0320), shl(224, 0x6f47ab5f))
                            revert(mload(0x0320), 4)
                        }
                        mstore(mload(0x0320), _231)
                        mstore(32, /** @src 0:41802:41810  "consumed" */ 0x02)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let dataSlot_65 := keccak256(mload(0x0320), 64)
                        mstore(mload(0x0320), value_52)
                        mstore(32, dataSlot_65)
                        let dataSlot_66 := keccak256(mload(0x0320), 64)
                        sstore(/** @src 0:41857:41882  "consumed[onBehalf][group]" */ dataSlot_66, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ or(and(sload(/** @src 0:41857:41882  "consumed[onBehalf][group]" */ dataSlot_66), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(0xffffffffffffffffffffffffffffffff)), _230))
                        /// @src 0:41906:41964  "EventsLib.SetConsumed(msg.sender, group, amount, onBehalf)"
                        let _232 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                        mstore(_232, _230)
                        /// @src 0:41906:41964  "EventsLib.SetConsumed(msg.sender, group, amount, onBehalf)"
                        log4(_232, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32, /** @src 0:41906:41964  "EventsLib.SetConsumed(msg.sender, group, amount, onBehalf)" */ 0xbf9d75f869db3f07b85b277c6ef4c58ee36ec3ec222303658012df26a9420d93, /** @src 0:41709:41719  "msg.sender" */ caller(), /** @src 0:41906:41964  "EventsLib.SetConsumed(msg.sender, group, amount, onBehalf)" */ value_52, _231)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        return(mload(0x0320), mload(0x0320))
                    }
                    case 0xf37e9ba4 {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let param_10, param_11 := abi_decode_bytes32t_uint256(calldatasize())
                        if iszero(/** @src 0:17596:17627  "msg.sender == tickSpacingSetter" */ eq(/** @src 0:17596:17606  "msg.sender" */ caller(), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(sload(/** @src 0:17610:17627  "tickSpacingSetter" */ 0x0c), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff)))
                        {
                            mstore(mload(0x0320), shl(225, 0x2a99a937))
                            revert(mload(0x0320), 4)
                        }
                        mstore(mload(0x0320), param_10)
                        mstore(0x20, /** @src 0:17671:17682  "marketState" */ 0x01)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        if /** @src 0:17671:17702  "marketState[id].tickSpacing > 0" */ iszero(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(shr(144, sload(/** @src 0:17671:17698  "marketState[id].tickSpacing" */ add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ keccak256(mload(0x0320), 64), /** @src 0:17671:17698  "marketState[id].tickSpacing" */ 2))), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xff))
                        {
                            mstore(mload(0x0320), shl(224, 0x96e13529))
                            revert(mload(0x0320), 4)
                        }
                        /// @src 0:17741:17812  "newTickSpacing > 0 && marketState[id].tickSpacing % newTickSpacing == 0"
                        let expr_79 := /** @src 0:17741:17759  "newTickSpacing > 0" */ iszero(iszero(param_11))
                        /// @src 0:17741:17812  "newTickSpacing > 0 && marketState[id].tickSpacing % newTickSpacing == 0"
                        if expr_79
                        {
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            mstore(mload(0x0320), param_10)
                            mstore(0x20, /** @src 0:17671:17682  "marketState" */ 0x01)
                            /// @src 0:17741:17812  "newTickSpacing > 0 && marketState[id].tickSpacing % newTickSpacing == 0"
                            expr_79 := /** @src 0:17763:17812  "marketState[id].tickSpacing % newTickSpacing == 0" */ iszero(/** @src 0:17763:17807  "marketState[id].tickSpacing % newTickSpacing" */ mod_uint256(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(shr(144, sload(/** @src 0:17763:17790  "marketState[id].tickSpacing" */ add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ keccak256(mload(0x0320), 64), /** @src 0:17671:17698  "marketState[id].tickSpacing" */ 2))), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xff), /** @src 0:17763:17807  "marketState[id].tickSpacing % newTickSpacing" */ param_11))
                        }
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        if iszero(expr_79)
                        {
                            mstore(mload(0x0320), shl(229, 0x013840ad))
                            revert(mload(0x0320), 4)
                        }
                        mstore(mload(0x0320), param_10)
                        mstore(0x20, /** @src 0:17671:17682  "marketState" */ 0x01)
                        /// @src 0:17963:17990  "marketState[id].tickSpacing"
                        let _233 := add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ keccak256(mload(0x0320), 64), /** @src 0:17671:17698  "marketState[id].tickSpacing" */ 2)
                        /// @src 7:1114:1115  "4"
                        let _234 := sload(_233)
                        sstore(_233, or(and(_234, not(shl(144, /** @src 7:190:194  "1e18" */ 255))), /** @src 7:1114:1115  "4" */ and(and(shl(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 144, /** @src 0:17993:18014  "uint8(newTickSpacing)" */ param_11), /** @src 7:1114:1115  "4" */ shl(144, /** @src 7:190:194  "1e18" */ 255)), /** @src 7:1114:1115  "4" */ shl(144, /** @src 7:190:194  "1e18" */ 255))))
                        /// @src 0:18029:18079  "EventsLib.SetMarketTickSpacing(id, newTickSpacing)"
                        let _235 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                        mstore(_235, param_11)
                        /// @src 0:18029:18079  "EventsLib.SetMarketTickSpacing(id, newTickSpacing)"
                        log2(_235, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x20, /** @src 0:18029:18079  "EventsLib.SetMarketTickSpacing(id, newTickSpacing)" */ 0x2fdb65e22fe4310a6b7ac73b0733cce84a7b9289fedcef0a7669bb4ea16a5919, param_10)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        return(mload(0x0320), mload(0x0320))
                    }
                    case 0xf3ad575e {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), 32)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let value0_25 := abi_decode_address_44122()
                        if iszero(/** @src 0:16191:16217  "msg.sender == configurator" */ eq(/** @src 0:16191:16201  "msg.sender" */ caller(), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(sload(/** @src 0:16205:16217  "configurator" */ 0x09), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff)))
                        {
                            mstore(mload(0x0320), shl(228, 0x033b71e1))
                            revert(mload(0x0320), 4)
                        }
                        let _236 := and(value0_25, 0xffffffffffffffffffffffffffffffffffffffff)
                        sstore(/** @src 0:16248:16288  "tickSpacingSetter = newTickSpacingSetter" */ 0x0c, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ or(and(sload(/** @src 0:16248:16288  "tickSpacingSetter = newTickSpacingSetter" */ 0x0c), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(0xffffffffffffffffffffffffffffffffffffffff)), _236))
                        /// @src 0:16303:16355  "EventsLib.SetTickSpacingSetter(newTickSpacingSetter)"
                        log2(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x0320), mload(0x0320), /** @src 0:16303:16355  "EventsLib.SetTickSpacingSetter(newTickSpacingSetter)" */ 0x14bcfba250c945e79a9901378a5d70dbcc7865cac69a6769f3a566efda01aea1, _236)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        return(mload(0x0320), mload(0x0320))
                    }
                    case 0xfc20106c {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), 32)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let value_54 := calldataload(4)
                        let memPtr_2 := mload(64)
                        finalize_allocation_44208(memPtr_2)
                        mstore(memPtr_2, mload(0x0320))
                        mstore(add(memPtr_2, 32), mload(0x0320))
                        mstore(add(memPtr_2, 64), mload(0x0320))
                        mstore(add(memPtr_2, 96), 96)
                        mstore(add(memPtr_2, 128), mload(0x0320))
                        mstore(add(memPtr_2, 160), mload(0x0320))
                        mstore(add(memPtr_2, 192), mload(0x0320))
                        mstore(add(memPtr_2, 224), mload(0x0320))
                        mstore(mload(0x0320), value_54)
                        mstore(32, 1)
                        if /** @src 0:51774:51805  "marketState[id].tickSpacing > 0" */ iszero(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(shr(144, sload(/** @src 0:51774:51801  "marketState[id].tickSpacing" */ add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ keccak256(mload(0x0320), 64), /** @src 0:51774:51801  "marketState[id].tickSpacing" */ 2))), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xff))
                        {
                            mstore(mload(0x0320), shl(224, 0x96e13529))
                            revert(mload(0x0320), 4)
                        }
                        let _237 := and(/** @src 0:51877:51888  "uint256(id)" */ value_54, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff)
                        let length_1 := extcodesize(_237)
                        let _238 := array_allocation_size_bytes(length_1)
                        let memPtr_3 := mload(64)
                        finalize_allocation(memPtr_3, _238)
                        mstore(memPtr_3, length_1)
                        let _239 := add(memPtr_3, 32)
                        extcodecopy(_237, _239, mload(0x0320), length_1)
                        /// @src 0:51907:51948  "abi.decode(create2Address.code, (Market))"
                        let _240 := add(memPtr_3, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(/** @src 0:51907:51948  "abi.decode(create2Address.code, (Market))" */ memPtr_3))
                        let _241 := add(_240, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 32)
                        if slt(sub(/** @src 0:51907:51948  "abi.decode(create2Address.code, (Market))" */ _240, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ memPtr_3), 32)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let offset_18 := mload(_239)
                        if gt(offset_18, 0xffffffffffffffff)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let _242 := add(memPtr_3, offset_18)
                        if slt(add(add(sub(/** @src 0:51907:51948  "abi.decode(create2Address.code, (Market))" */ _240, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _242), not(31)), 32), 256)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let memPtr_4 := mload(64)
                        finalize_allocation_44208(memPtr_4)
                        mstore(memPtr_4, mload(add(_242, 32)))
                        mstore(add(memPtr_4, 32), abi_decode_address_fromMemory(add(_242, 64)))
                        mstore(add(memPtr_4, 64), abi_decode_address_fromMemory(add(_242, 96)))
                        let offset_19 := mload(add(_242, 128))
                        if gt(offset_19, 0xffffffffffffffff)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let _243 := add(add(_242, offset_19), 32)
                        if iszero(slt(add(_243, 0x1f), _241))
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let length_2 := mload(_243)
                        let _244 := array_allocation_size_array_struct_CollateralParams_dyn(length_2)
                        let memPtr_5 := mload(64)
                        finalize_allocation(memPtr_5, _244)
                        let dst := memPtr_5
                        mstore(memPtr_5, length_2)
                        dst := add(memPtr_5, 32)
                        let srcEnd := add(add(_243, shl(7, length_2)), 32)
                        if gt(srcEnd, _241)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        let src := add(_243, 32)
                        for { } lt(src, srcEnd) { src := add(src, 128) }
                        {
                            if slt(add(sub(/** @src 0:51907:51948  "abi.decode(create2Address.code, (Market))" */ _240, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ src), 32), 128)
                            {
                                revert(mload(0x0320), mload(0x0320))
                            }
                            let memPtr_6 := mload(64)
                            finalize_allocation_44210(memPtr_6)
                            mstore(memPtr_6, abi_decode_address_fromMemory(src))
                            mstore(add(memPtr_6, 32), mload(add(src, 32)))
                            mstore(add(memPtr_6, 64), mload(add(src, 64)))
                            mstore(add(memPtr_6, 96), abi_decode_address_fromMemory(add(src, 96)))
                            mstore(dst, memPtr_6)
                            dst := add(dst, 32)
                        }
                        mstore(add(memPtr_4, 96), memPtr_5)
                        mstore(add(memPtr_4, 128), mload(add(_242, 160)))
                        mstore(add(memPtr_4, 160), mload(add(_242, 192)))
                        mstore(add(memPtr_4, 192), abi_decode_address_fromMemory(add(_242, 224)))
                        mstore(add(memPtr_4, 224), abi_decode_address_fromMemory(add(_242, 256)))
                        let memPos_34 := mload(64)
                        mstore(memPos_34, 32)
                        return(memPos_34, sub(abi_encode_struct_Market(memPtr_4, add(memPos_34, 32)), memPos_34))
                    }
                    case 0xfd2ff327 {
                        if callvalue()
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        if slt(add(calldatasize(), not(3)), 32)
                        {
                            revert(mload(0x0320), mload(0x0320))
                        }
                        mstore(mload(0x0320), calldataload(4))
                        mstore(32, 1)
                        let _245 := shr(128, sload(/** @src 0:53427:53462  "marketState[id].continuousFeeCredit" */ add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ keccak256(mload(0x0320), 64), 1)))
                        let memPos_35 := mload(64)
                        mstore(memPos_35, _245)
                        return(memPos_35, 32)
                    }
                }
                revert(0, 0)
            }
            function abi_decode_address_44120() -> value
            {
                value := calldataload(36)
                if iszero(eq(value, and(value, 0xffffffffffffffffffffffffffffffffffffffff))) { revert(0, 0) }
            }
            function abi_decode_address_44122() -> value
            {
                value := calldataload(4)
                if iszero(eq(value, and(value, 0xffffffffffffffffffffffffffffffffffffffff))) { revert(0, 0) }
            }
            function abi_decode_address_44128() -> value
            {
                value := calldataload(68)
                if iszero(eq(value, and(value, 0xffffffffffffffffffffffffffffffffffffffff))) { revert(0, 0) }
            }
            function abi_decode_address_44129() -> value
            {
                value := calldataload(100)
                if iszero(eq(value, and(value, 0xffffffffffffffffffffffffffffffffffffffff))) { revert(0, 0) }
            }
            function abi_decode_address_44141() -> value
            {
                value := calldataload(132)
                if iszero(eq(value, and(value, 0xffffffffffffffffffffffffffffffffffffffff))) { revert(0, 0) }
            }
            function abi_decode_address(offset) -> value
            {
                value := calldataload(offset)
                if iszero(eq(value, and(value, 0xffffffffffffffffffffffffffffffffffffffff))) { revert(0, 0) }
            }
            function mapping_index_access_mapping_address_uint32_of_address(key) -> dataSlot
            {
                mstore(0, and(key, 0xffffffffffffffffffffffffffffffffffffffff))
                mstore(0x20, /** @src 0:23238:23250  "isAuthorized" */ 0x03)
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                dataSlot := keccak256(0, 0x40)
            }
            function mapping_index_access_mapping_address__uint32__of_address(key) -> dataSlot
            {
                mstore(0, and(key, 0xffffffffffffffffffffffffffffffffffffffff))
                mstore(0x20, /** @src 0:23593:23619  "_marketState.continuousFee" */ 2)
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                dataSlot := keccak256(0, 0x40)
            }
            function finalize_allocation_44126(memPtr)
            {
                let newFreePtr := add(memPtr, 224)
                if or(gt(newFreePtr, 0xffffffffffffffff), lt(newFreePtr, memPtr))
                {
                    mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(224, 0x4e487b71))
                    mstore(4, 0x41)
                    revert(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x24)
                }
                mstore(64, newFreePtr)
            }
            function finalize_allocation_44208(memPtr)
            {
                let newFreePtr := add(memPtr, 256)
                if or(gt(newFreePtr, 0xffffffffffffffff), lt(newFreePtr, memPtr))
                {
                    mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(224, 0x4e487b71))
                    mstore(4, 0x41)
                    revert(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x24)
                }
                mstore(64, newFreePtr)
            }
            function finalize_allocation_44210(memPtr)
            {
                let newFreePtr := add(memPtr, 128)
                if or(gt(newFreePtr, 0xffffffffffffffff), lt(newFreePtr, memPtr))
                {
                    mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(224, 0x4e487b71))
                    mstore(4, 0x41)
                    revert(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x24)
                }
                mstore(64, newFreePtr)
            }
            function finalize_allocation(memPtr, size)
            {
                let newFreePtr := add(memPtr, and(add(size, 31), not(31)))
                if or(gt(newFreePtr, 0xffffffffffffffff), lt(newFreePtr, memPtr))
                {
                    mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(224, 0x4e487b71))
                    mstore(4, 0x41)
                    revert(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x24)
                }
                mstore(64, newFreePtr)
            }
            function array_allocation_size_array_struct_CollateralParams_dyn(length) -> size
            {
                if gt(length, 0xffffffffffffffff)
                {
                    mstore(0, shl(224, 0x4e487b71))
                    mstore(4, 0x41)
                    revert(0, 0x24)
                }
                size := add(shl(5, length), 0x20)
            }
            function abi_decode_struct_CollateralParams(headStart, end) -> value
            {
                if slt(sub(end, headStart), 0x80) { revert(0, 0) }
                let memPtr := mload(64)
                finalize_allocation_44210(memPtr)
                value := memPtr
                mstore(memPtr, abi_decode_address(headStart))
                mstore(add(memPtr, 32), calldataload(add(headStart, 32)))
                mstore(add(memPtr, 64), calldataload(add(headStart, 64)))
                mstore(add(memPtr, 96), abi_decode_address(add(headStart, 96)))
            }
            function abi_decode_struct_Market(headStart, end) -> value
            {
                if slt(sub(end, headStart), 0x0100) { revert(0, 0) }
                let memPtr := mload(64)
                finalize_allocation_44208(memPtr)
                value := memPtr
                mstore(memPtr, calldataload(headStart))
                mstore(add(memPtr, 32), abi_decode_address(add(headStart, 32)))
                mstore(add(memPtr, 64), abi_decode_address(add(headStart, 64)))
                let offset := calldataload(add(headStart, 96))
                if gt(offset, 0xffffffffffffffff)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                let _1 := add(headStart, offset)
                if iszero(slt(add(_1, 0x1f), end))
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                let length := calldataload(_1)
                let _2 := array_allocation_size_array_struct_CollateralParams_dyn(length)
                let memPtr_1 := mload(64)
                finalize_allocation(memPtr_1, _2)
                let dst := memPtr_1
                mstore(memPtr_1, length)
                dst := add(memPtr_1, 32)
                let srcEnd := add(add(_1, shl(7, length)), 32)
                if gt(srcEnd, end)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                let src := add(_1, 32)
                for { } lt(src, srcEnd) { src := add(src, 0x80) }
                {
                    mstore(dst, abi_decode_struct_CollateralParams(src, end))
                    dst := add(dst, 32)
                }
                mstore(add(memPtr, 96), memPtr_1)
                mstore(add(memPtr, 0x80), calldataload(add(headStart, 0x80)))
                mstore(add(memPtr, 160), calldataload(add(headStart, 160)))
                mstore(add(memPtr, 192), abi_decode_address(add(headStart, 192)))
                mstore(add(memPtr, 224), abi_decode_address(add(headStart, 224)))
            }
            function abi_decode_bytes32t_uint256(dataEnd) -> value0, value1
            {
                if slt(add(dataEnd, not(3)), 64) { revert(0, 0) }
                value0 := calldataload(4)
                value1 := calldataload(36)
            }
            function abi_decode_array_address_dyn_calldata(offset, end) -> arrayPos, length
            {
                if iszero(slt(add(offset, 0x1f), end)) { revert(0, 0) }
                length := calldataload(offset)
                if gt(length, 0xffffffffffffffff) { revert(0, 0) }
                arrayPos := add(offset, 0x20)
                if gt(add(add(offset, shl(5, length)), 0x20), end) { revert(0, 0) }
            }
            function abi_decode_bytes_calldata(offset, end) -> arrayPos, length
            {
                if iszero(slt(add(offset, 0x1f), end)) { revert(0, 0) }
                length := calldataload(offset)
                if gt(length, 0xffffffffffffffff) { revert(0, 0) }
                arrayPos := add(offset, 0x20)
                if gt(add(add(offset, length), 0x20), end) { revert(0, 0) }
            }
            function abi_encode_uint128_uint128_uint128(headStart, value0, value1, value2) -> tail
            {
                tail := add(headStart, 96)
                mstore(headStart, and(value0, 0xffffffffffffffffffffffffffffffff))
                mstore(add(headStart, 32), and(value1, 0xffffffffffffffffffffffffffffffff))
                mstore(add(headStart, 64), and(value2, 0xffffffffffffffffffffffffffffffff))
            }
            function abi_decode_struct_Markett_bytes32t_address(dataEnd) -> value0, value1, value2
            {
                if slt(add(dataEnd, not(3)), 96) { revert(0, 0) }
                let offset := calldataload(4)
                if gt(offset, 0xffffffffffffffff) { revert(0, 0) }
                value0 := abi_decode_struct_Market(add(4, offset), dataEnd)
                value1 := calldataload(36)
                let value := /** @src -1:-1:-1 */ 0
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                value := calldataload(68)
                if iszero(eq(value, and(value, 0xffffffffffffffffffffffffffffffffffffffff))) { revert(0, 0) }
                value2 := value
            }
            function abi_decode_bool(offset) -> value
            {
                value := calldataload(offset)
                if iszero(eq(value, iszero(iszero(value)))) { revert(0, 0) }
            }
            function array_allocation_size_bytes(length) -> size
            {
                if gt(length, 0xffffffffffffffff)
                {
                    mstore(0, shl(224, 0x4e487b71))
                    mstore(4, 0x41)
                    revert(0, 0x24)
                }
                size := add(and(add(length, 31), not(31)), 0x20)
            }
            function abi_decode_bytes(offset, end) -> array
            {
                if iszero(slt(add(offset, 0x1f), end)) { revert(0, 0) }
                let length := calldataload(offset)
                let _1 := array_allocation_size_bytes(length)
                let memPtr := mload(64)
                finalize_allocation(memPtr, _1)
                mstore(memPtr, length)
                if gt(add(add(offset, length), 0x20), end)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                calldatacopy(add(memPtr, 0x20), add(offset, 0x20), length)
                mstore(add(add(memPtr, length), 0x20), /** @src -1:-1:-1 */ 0)
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                array := memPtr
            }
            function abi_decode_uint128(offset) -> value
            {
                value := calldataload(offset)
                if iszero(eq(value, and(value, 0xffffffffffffffffffffffffffffffff))) { revert(0, 0) }
            }
            function storage_array_index_access_uint(array, index) -> slot, offset
            {
                if iszero(lt(index, 0x07))
                {
                    mstore(0, shl(224, 0x4e487b71))
                    mstore(4, 0x32)
                    revert(0, 0x24)
                }
                slot := add(array, shr(4, index))
                offset := and(shl(1, index), 30)
            }
            function abi_encode_struct_Market(value, pos) -> end
            {
                let tail := add(pos, 0x0100)
                mstore(pos, mload(value))
                mstore(add(pos, 0x20), and(mload(add(value, 0x20)), 0xffffffffffffffffffffffffffffffffffffffff))
                mstore(add(pos, 0x40), and(mload(add(value, 0x40)), 0xffffffffffffffffffffffffffffffffffffffff))
                let memberValue0 := mload(add(value, 0x60))
                mstore(add(pos, 0x60), 0x0100)
                let pos_1 := tail
                let length := mload(memberValue0)
                mstore(tail, length)
                pos_1 := add(pos, 288)
                let srcPtr := add(memberValue0, 0x20)
                let i := 0
                for { } lt(i, length) { i := add(i, 1) }
                {
                    let _1 := mload(srcPtr)
                    mstore(pos_1, and(mload(_1), 0xffffffffffffffffffffffffffffffffffffffff))
                    mstore(add(pos_1, 0x20), mload(add(_1, 0x20)))
                    mstore(add(pos_1, 0x40), mload(add(_1, 0x40)))
                    mstore(add(pos_1, 0x60), and(mload(add(_1, 0x60)), 0xffffffffffffffffffffffffffffffffffffffff))
                    pos_1 := add(pos_1, 0x80)
                    srcPtr := add(srcPtr, 0x20)
                }
                mstore(add(pos, 0x80), mload(add(value, 0x80)))
                mstore(add(pos, 0xa0), mload(add(value, 0xa0)))
                mstore(add(pos, 0xc0), and(mload(add(value, 0xc0)), 0xffffffffffffffffffffffffffffffffffffffff))
                mstore(add(pos, 0xe0), and(mload(add(value, 0xe0)), 0xffffffffffffffffffffffffffffffffffffffff))
                end := pos_1
            }
            function checked_div_uint256(x, y) -> r
            {
                if iszero(y)
                {
                    mstore(0, shl(224, 0x4e487b71))
                    mstore(4, 0x12)
                    revert(0, 0x24)
                }
                r := div(x, y)
            }
            function checked_sub_uint256_44174(y) -> diff
            {
                diff := sub(0xffffffffffffffffffffffffffffffff, y)
                if gt(diff, 0xffffffffffffffffffffffffffffffff)
                {
                    mstore(0, shl(224, 0x4e487b71))
                    mstore(4, 0x11)
                    revert(0, 0x24)
                }
            }
            function checked_sub_uint256(x, y) -> diff
            {
                diff := sub(x, y)
                if gt(diff, x)
                {
                    mstore(0, shl(224, 0x4e487b71))
                    mstore(4, 0x11)
                    revert(0, 0x24)
                }
            }
            function memory_array_index_access_struct_CollateralParams_dyn(baseRef, index) -> addr
            {
                if iszero(lt(index, mload(baseRef)))
                {
                    mstore(0, shl(224, 0x4e487b71))
                    mstore(4, 0x32)
                    revert(0, 0x24)
                }
                addr := add(add(baseRef, shl(5, index)), 32)
            }
            function storage_array_index_access_uint128_(array, index) -> slot, offset
            {
                if iszero(lt(index, 0x80))
                {
                    mstore(0, shl(224, 0x4e487b71))
                    mstore(4, 0x32)
                    revert(0, 0x24)
                }
                slot := add(array, shr(1, index))
                offset := and(shl(4, index), 16)
            }
            function update_storage_value_offset_uint128_to_uint128(slot, value)
            {
                let _1 := sload(slot)
                sstore(slot, or(and(_1, 0xffffffffffffffffffffffffffffffff), and(shl(128, value), not(0xffffffffffffffffffffffffffffffff))))
            }
            /// @src 7:892:894  "16"
            function checked_add_uint256_44170(x) -> sum
            {
                sum := add(x, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xc097ce7bc90715b34b9f0fffffffff)
                /// @src 7:892:894  "16"
                if gt(x, sum)
                {
                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                    mstore(0, shl(224, 0x4e487b71))
                    mstore(4, 0x11)
                    revert(0, 0x24)
                }
            }
            /// @src 7:892:894  "16"
            function checked_add_uint256(x, y) -> sum
            {
                sum := add(x, y)
                if gt(x, sum)
                {
                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                    mstore(0, shl(224, 0x4e487b71))
                    mstore(4, 0x11)
                    revert(0, 0x24)
                }
            }
            /// @src 7:892:894  "16"
            function update_storage_value_uint128_to_uint128(slot, offset, value)
            {
                let _1 := sload(slot)
                let shiftBits := shl(3, offset)
                sstore(slot, or(and(_1, not(shl(shiftBits, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff))), /** @src 7:892:894  "16" */ shl(shiftBits, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 7:892:894  "16" */ value, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff))))
            }
            /// @src 7:892:894  "16"
            function abi_encode_address_uint256(headStart, value0, value1) -> tail
            {
                tail := add(headStart, 64)
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                mstore(headStart, and(value0, 0xffffffffffffffffffffffffffffffffffffffff))
                mstore(/** @src 7:892:894  "16" */ add(headStart, 32), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ value1)
            }
            function update_storage_value_offset_uint32_to_uint32(slot, value)
            {
                let _1 := sload(slot)
                sstore(slot, or(and(_1, not(0xffffffff0000000000000000000000000000)), and(shl(112, value), 0xffffffff0000000000000000000000000000)))
            }
            function abi_encode_array_address_dyn_calldata(value, length, pos) -> end
            {
                mstore(pos, length)
                pos := add(pos, 0x20)
                let srcPtr := value
                let i := /** @src -1:-1:-1 */ 0
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                for { } lt(i, length) { i := add(i, 1) }
                {
                    mstore(pos, and(abi_decode_address(srcPtr), 0xffffffffffffffffffffffffffffffffffffffff))
                    pos := add(pos, 0x20)
                    srcPtr := add(srcPtr, 0x20)
                }
                end := pos
            }
            function abi_encode_array_uint256_dyn_calldata(start, length, pos) -> end
            {
                mstore(pos, length)
                if gt(length, 0x07ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                let length_1 := shl(5, length)
                calldatacopy(add(pos, 0x20), start, length_1)
                end := add(add(pos, length_1), 0x20)
            }
            function calldata_array_index_access_address_dyn_calldata(base_ref, length, index) -> addr
            {
                if iszero(lt(index, length))
                {
                    mstore(0, shl(224, 0x4e487b71))
                    mstore(4, 0x32)
                    revert(0, 0x24)
                }
                addr := add(base_ref, shl(5, index))
            }
            function read_from_calldatat_address(ptr) -> returnValue
            {
                let value := calldataload(ptr)
                if iszero(eq(value, and(value, 0xffffffffffffffffffffffffffffffffffffffff))) { revert(0, 0) }
                returnValue := value
            }
            function abi_encode_bytes_calldata(start, length, pos) -> end
            {
                mstore(pos, length)
                calldatacopy(add(pos, 0x20), start, length)
                mstore(add(add(pos, length), 0x20), /** @src -1:-1:-1 */ 0)
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                end := add(add(pos, and(add(length, 31), not(31))), 0x20)
            }
            function checked_sub_uint128(x, y) -> diff
            {
                diff := sub(and(x, 0xffffffffffffffffffffffffffffffff), and(y, 0xffffffffffffffffffffffffffffffff))
                if gt(diff, 0xffffffffffffffffffffffffffffffff)
                {
                    mstore(0, shl(224, 0x4e487b71))
                    mstore(4, 0x11)
                    revert(0, 0x24)
                }
            }
            /// @ast-id 3655 @src 0:49036:49919  "function isHealthy(Market memory market, bytes32 id, address borrower) public view returns (bool) {..."
            function fun_isHealthy(var_market_3562_mpos, var_id, var_borrower) -> var
            {
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                mstore(0, var_id)
                mstore(0x20, 0)
                let dataSlot := keccak256(0, 0x40)
                /// @src 0:49173:49195  "position[id][borrower]"
                let dataSlot_1 := /** @src -1:-1:-1 */ 0
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:49173:49195  "position[id][borrower]" */ var_borrower, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                mstore(0x20, /** @src 0:49173:49185  "position[id]" */ dataSlot)
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                dataSlot_1 := keccak256(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x40)
                let _1 := sload(/** @src 0:49221:49235  "_position.debt" */ add(/** @src 0:49173:49195  "position[id][borrower]" */ dataSlot_1, /** @src 0:49221:49235  "_position.debt" */ 2))
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                let cleaned := and(_1, 0xffffffffffffffffffffffffffffffff)
                /// @src 0:49245:49260  "uint256 maxDebt"
                let var_maxDebt := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                /// @src 0:49245:49260  "uint256 maxDebt"
                var_maxDebt := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                /// @src 0:49270:49880  "if (_debt > 0) {..."
                if /** @src 0:49274:49283  "_debt > 0" */ iszero(iszero(cleaned))
                /// @src 0:49270:49880  "if (_debt > 0) {..."
                {
                    /// @src 0:49299:49353  "uint128 _collateralBitmap = _position.collateralBitmap"
                    let var_collateralBitmap := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shr(128, _1)
                    /// @src 0:49647:49667  "_position.collateral"
                    let _2 := add(/** @src 0:49173:49195  "position[id][borrower]" */ dataSlot_1, /** @src 0:49647:49667  "_position.collateral" */ 3)
                    /// @src 0:49367:49870  "while (_collateralBitmap != 0) {..."
                    for { }
                    /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:49374:49396  "_collateralBitmap != 0" */ var_collateralBitmap, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)
                    /// @src 0:49367:49870  "while (_collateralBitmap != 0) {..."
                    { }
                    {
                        /// @src 0:49428:49459  "UtilsLib.msb(_collateralBitmap)"
                        let expr := /** @src 12:1643:1704  "assembly {..." */ sub(255, clz(/** @src 0:49428:49459  "UtilsLib.msb(_collateralBitmap)" */ var_collateralBitmap))
                        /// @src 0:49519:49545  "market.collateralParams[i]"
                        let _mpos := mload(memory_array_index_access_struct_CollateralParams_dyn(/** @src 0:49519:49542  "market.collateralParams" */ mload(add(var_market_3562_mpos, 96)), /** @src 0:49519:49545  "market.collateralParams[i]" */ expr))
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let cleaned_1 := and(mload(/** @src 0:49587:49609  "collateralParam.oracle" */ add(_mpos, /** @src 0:49519:49542  "market.collateralParams" */ 96)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff)
                        /// @src 0:49579:49618  "IOracle(collateralParam.oracle).price()"
                        let _3 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x40)
                        /// @src 0:49579:49618  "IOracle(collateralParam.oracle).price()"
                        mstore(_3, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(225, 0x501ad8ff))
                        /// @src 0:49579:49618  "IOracle(collateralParam.oracle).price()"
                        let _4 := staticcall(gas(), cleaned_1, _3, 4, _3, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x20)
                        /// @src 0:49579:49618  "IOracle(collateralParam.oracle).price()"
                        if iszero(_4)
                        {
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let pos := mload(0x40)
                            returndatacopy(pos, 0, returndatasize())
                            revert(pos, returndatasize())
                        }
                        /// @src 0:49579:49618  "IOracle(collateralParam.oracle).price()"
                        let expr_1 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                        /// @src 0:49579:49618  "IOracle(collateralParam.oracle).price()"
                        if _4
                        {
                            let _5 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x20
                            /// @src 0:49579:49618  "IOracle(collateralParam.oracle).price()"
                            if gt(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _5, /** @src 0:49579:49618  "IOracle(collateralParam.oracle).price()" */ returndatasize()) { _5 := returndatasize() }
                            finalize_allocation(_3, _5)
                            let value0 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                            if slt(sub(/** @src 0:49579:49618  "IOracle(collateralParam.oracle).price()" */ add(_3, _5), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _3), 32) { revert(0, 0) }
                            value0 := mload(_3)
                            /// @src 0:49579:49618  "IOracle(collateralParam.oracle).price()"
                            expr_1 := value0
                        }
                        /// @src 0:49647:49670  "_position.collateral[i]"
                        let _6, _7 := storage_array_index_access_uint128_(_2, expr)
                        /// @src 12:653:658  "x * y"
                        let _8 := checked_mul_uint256(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(shr(shl(/** @src 0:49647:49667  "_position.collateral" */ 3, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _7), sload(/** @src 0:49647:49670  "_position.collateral[i]" */ _6)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff), /** @src 12:653:658  "x * y" */ expr_1)
                        /// @src 12:652:663  "(x * y) / d"
                        let r := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                        let _9 := 0
                        _9 := 0
                        r := div(_8, /** @src 7:234:238  "1e36" */ 0xc097ce7bc90715b34b9f1000000000)
                        /// @src 12:653:658  "x * y"
                        let _10 := checked_mul_uint256(r, /** @src 7:234:238  "1e36" */ mload(/** @src 0:49762:49782  "collateralParam.lltv" */ add(_mpos, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x20)))
                        /// @src 12:652:663  "(x * y) / d"
                        let r_1 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                        let _11 := 0
                        _11 := 0
                        r_1 := div(_10, /** @src 7:190:194  "1e18" */ 0x0de0b6b3a7640000)
                        /// @src 0:49636:49788  "maxDebt += _position.collateral[i]..."
                        var_maxDebt := checked_add_uint256(var_maxDebt, /** @src 0:49647:49788  "_position.collateral[i]..." */ r_1)
                        /// @src 0:49806:49855  "_collateralBitmap = _collateralBitmap.clearBit(i)"
                        var_collateralBitmap := /** @src 12:2170:2190  "bitmap & ~(1 << bit)" */ and(and(/** @src 0:49374:49396  "_collateralBitmap != 0" */ var_collateralBitmap, /** @src 12:2179:2190  "~(1 << bit)" */ not(/** @src 7:892:894  "16" */ shl(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ expr, /** @src 12:2181:2182  "1" */ 0x01))), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)
                    }
                }
                /// @src 0:49889:49912  "return maxDebt >= _debt"
                var := /** @src 0:49896:49912  "maxDebt >= _debt" */ iszero(lt(var_maxDebt, cleaned))
            }
            /// @src 7:263:267  "1e12"
            function mod_uint256(x, y) -> r
            {
                if iszero(y)
                {
                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                    mstore(0, shl(224, 0x4e487b71))
                    mstore(4, 0x12)
                    revert(0, 0x24)
                }
                /// @src 7:263:267  "1e12"
                r := mod(x, y)
            }
            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
            function abi_encode_bytes(value, pos) -> end
            {
                let length := mload(value)
                mstore(pos, length)
                mcopy(add(pos, 0x20), add(value, 0x20), length)
                mstore(add(add(pos, length), 0x20), /** @src -1:-1:-1 */ 0)
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                end := add(add(pos, and(add(length, 31), not(31))), 0x20)
            }
            function abi_encode_struct_Offer(value, pos) -> end
            {
                let memberValue0 := mload(value)
                mstore(pos, 0x01e0)
                let tail := abi_encode_struct_Market(memberValue0, add(pos, 0x01e0))
                mstore(add(pos, 0x20), iszero(iszero(mload(add(value, 0x20)))))
                mstore(add(pos, 0x40), and(mload(add(value, 0x40)), 0xffffffffffffffffffffffffffffffffffffffff))
                mstore(add(pos, 0x60), mload(add(value, 0x60)))
                mstore(add(pos, 0x80), mload(add(value, 0x80)))
                mstore(add(pos, 0xa0), mload(add(value, 0xa0)))
                mstore(add(pos, 0xc0), mload(add(value, 0xc0)))
                mstore(add(pos, 0xe0), and(mload(add(value, 0xe0)), 0xffffffffffffffffffffffffffffffffffffffff))
                let memberValue0_1 := mload(add(value, 0x0100))
                mstore(add(pos, 0x0100), sub(tail, pos))
                let tail_1 := abi_encode_bytes(memberValue0_1, tail)
                mstore(add(pos, 0x0120), and(mload(add(value, 0x0120)), 0xffffffffffffffffffffffffffffffffffffffff))
                mstore(add(pos, 0x0140), and(mload(add(value, 0x0140)), 0xffffffffffffffffffffffffffffffffffffffff))
                mstore(add(pos, 0x0160), iszero(iszero(mload(add(value, 0x0160)))))
                mstore(add(pos, 0x0180), and(mload(add(value, 0x0180)), 0xffffffffffffffffffffffffffffffff))
                mstore(add(pos, 0x01a0), and(mload(add(value, 0x01a0)), 0xffffffffffffffffffffffffffffffff))
                mstore(add(pos, 0x01c0), mload(add(value, 0x01c0)))
                end := tail_1
            }
            function checked_mul_uint256_44172(x) -> product
            {
                product := mul(x, /** @src 7:190:194  "1e18" */ 0x0de0b6b3a7640000)
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                if iszero(or(iszero(x), eq(/** @src 7:190:194  "1e18" */ 0x0de0b6b3a7640000, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ div(product, x))))
                {
                    mstore(0, shl(224, 0x4e487b71))
                    mstore(4, 0x11)
                    revert(0, 0x24)
                }
            }
            function checked_mul_uint256(x, y) -> product
            {
                product := mul(x, y)
                if iszero(or(iszero(x), eq(y, div(product, x))))
                {
                    mstore(0, shl(224, 0x4e487b71))
                    mstore(4, 0x11)
                    revert(0, 0x24)
                }
            }
            function abi_decode_bool_fromMemory(headStart, dataEnd) -> value0
            {
                if slt(sub(dataEnd, headStart), 32) { revert(0, 0) }
                let value := mload(headStart)
                if iszero(eq(value, iszero(iszero(value))))
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                value0 := value
            }
            function checked_add_uint128(x, y) -> sum
            {
                sum := add(and(x, 0xffffffffffffffffffffffffffffffff), and(y, 0xffffffffffffffffffffffffffffffff))
                if gt(sum, 0xffffffffffffffffffffffffffffffff)
                {
                    mstore(0, shl(224, 0x4e487b71))
                    mstore(4, 0x11)
                    revert(0, 0x24)
                }
            }
            function update_storage_value_offset_12_uint16_to_uint16(slot, value)
            {
                let _1 := sload(slot)
                sstore(slot, or(and(_1, not(0xffff000000000000000000000000)), and(shl(96, value), 0xffff000000000000000000000000)))
            }
            function update_storage_value_offset_uint16_to_uint16(slot, value)
            {
                let _1 := sload(slot)
                sstore(slot, or(and(_1, not(0xffff00000000000000000000)), and(shl(80, value), 0xffff00000000000000000000)))
            }
            function update_storage_value_offset_8_uint16_to_uint16(slot, value)
            {
                let _1 := sload(slot)
                sstore(slot, or(and(_1, not(0xffff0000000000000000)), and(shl(64, value), 0xffff0000000000000000)))
            }
            function update_storage_value_offset_t_uint16_to_t_uint16(slot, value)
            {
                let _1 := sload(slot)
                sstore(slot, or(and(_1, not(0xffff000000000000)), and(shl(48, value), 0xffff000000000000)))
            }
            function update_storage_value_offset_4_uint16_to_uint16(slot, value)
            {
                let _1 := sload(slot)
                sstore(slot, or(and(_1, not(0xffff00000000)), and(shl(32, value), 0xffff00000000)))
            }
            function update_storage_value_offset_2_uint16_to_uint16(slot, value)
            {
                let _1 := sload(slot)
                sstore(slot, or(and(_1, not(0xffff0000)), and(shl(16, value), 0xffff0000)))
            }
            function access_calldata_tail_array_struct_CollateralParams_calldata_dyn_calldata(base_ref, ptr_to_tail) -> addr, length
            {
                let rel_offset_of_tail := calldataload(ptr_to_tail)
                if iszero(slt(rel_offset_of_tail, add(sub(calldatasize(), base_ref), not(30)))) { revert(0, 0) }
                let addr_1 := add(base_ref, rel_offset_of_tail)
                length := calldataload(addr_1)
                if gt(length, 0xffffffffffffffff) { revert(0, 0) }
                addr := add(addr_1, 0x20)
                if sgt(addr, sub(calldatasize(), shl(7, length))) { revert(0, 0) }
            }
            function calldata_array_index_access_struct_CollateralParams_calldata_dyn_calldata(base_ref, length, index) -> addr
            {
                if iszero(lt(index, length))
                {
                    mstore(0, shl(224, 0x4e487b71))
                    mstore(4, 0x32)
                    revert(0, 0x24)
                }
                addr := add(base_ref, shl(7, index))
            }
            /// @ast-id 3278 @src 0:43229:45666  "function touchMarket(Market memory market) public returns (bytes32) {..."
            function fun_touchMarket(var_market_2995_mpos) -> var
            {
                /// @src 9:1486:1501  "market.midnight"
                let _1 := add(var_market_2995_mpos, 32)
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                let _2 := mload(/** @src 9:1486:1501  "market.midnight" */ _1)
                /// @src 9:1574:1588  "SSTORE2_PREFIX"
                let expr_mpos := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ copy_literal_to_memory_a55ffd6cc2b0b507f8827f3c680fa2adb9285b64bf7fb098798ce57c2156693f()
                /// @src 9:1590:1608  "abi.encode(market)"
                let expr_mpos_1 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                /// @src 9:1590:1608  "abi.encode(market)"
                let _3 := add(expr_mpos_1, /** @src 9:1486:1501  "market.midnight" */ 32)
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                mstore(_3, /** @src 9:1486:1501  "market.midnight" */ 32)
                /// @src 9:1590:1608  "abi.encode(market)"
                let _4 := sub(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ abi_encode_struct_Market(var_market_2995_mpos, add(/** @src 9:1590:1608  "abi.encode(market)" */ expr_mpos_1, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 64)), /** @src 9:1590:1608  "abi.encode(market)" */ expr_mpos_1)
                mstore(expr_mpos_1, add(_4, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(31)))
                /// @src 9:1590:1608  "abi.encode(market)"
                finalize_allocation(expr_mpos_1, _4)
                /// @src 9:1557:1609  "abi.encodePacked(SSTORE2_PREFIX, abi.encode(market))"
                let expr_mpos_2 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                /// @src 9:1557:1609  "abi.encodePacked(SSTORE2_PREFIX, abi.encode(market))"
                let _5 := add(expr_mpos_2, /** @src 9:1486:1501  "market.midnight" */ 32)
                /// @src 9:1154:1181  "hex\"600b380380600b5f395ff3\""
                let length := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(/** @src 9:1154:1181  "hex\"600b380380600b5f395ff3\"" */ expr_mpos)
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                mcopy(_5, /** @src 9:1154:1181  "hex\"600b380380600b5f395ff3\"" */ add(expr_mpos, /** @src 9:1486:1501  "market.midnight" */ 32), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ length)
                let _6 := add(/** @src 9:1557:1609  "abi.encodePacked(SSTORE2_PREFIX, abi.encode(market))" */ expr_mpos_2, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ length)
                let _7 := add(_6, /** @src 9:1486:1501  "market.midnight" */ 32)
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                mstore(_7, 0)
                /// @src 9:1154:1181  "hex\"600b380380600b5f395ff3\""
                let length_1 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(/** @src 9:1154:1181  "hex\"600b380380600b5f395ff3\"" */ expr_mpos_1)
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                mcopy(_7, _3, length_1)
                let _8 := add(add(_6, length_1), /** @src 9:1486:1501  "market.midnight" */ 32)
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                mstore(_8, 0)
                /// @src 9:1557:1609  "abi.encodePacked(SSTORE2_PREFIX, abi.encode(market))"
                let _9 := sub(_8, expr_mpos_2)
                mstore(expr_mpos_2, add(_9, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(31)))
                /// @src 9:1557:1609  "abi.encodePacked(SSTORE2_PREFIX, abi.encode(market))"
                finalize_allocation(expr_mpos_2, _9)
                /// @src 9:1547:1610  "keccak256(abi.encodePacked(SSTORE2_PREFIX, abi.encode(market)))"
                let expr := keccak256(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _5, mload(/** @src 9:1547:1610  "keccak256(abi.encodePacked(SSTORE2_PREFIX, abi.encode(market)))" */ expr_mpos_2))
                /// @src 9:1423:1624  "abi.encodePacked(..."
                let expr_mpos_3 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                /// @src 9:1423:1624  "abi.encodePacked(..."
                let _10 := add(expr_mpos_3, /** @src 9:1486:1501  "market.midnight" */ 32)
                /// @src 9:1154:1181  "hex\"600b380380600b5f395ff3\""
                mstore(_10, shl(248, /** @src 7:190:194  "1e18" */ 255))
                /// @src 9:1154:1181  "hex\"600b380380600b5f395ff3\""
                mstore(add(/** @src 9:1423:1624  "abi.encodePacked(..." */ expr_mpos_3, /** @src 9:1154:1181  "hex\"600b380380600b5f395ff3\"" */ 33), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(shl(96, _2), not(0xffffffffffffffffffffffff)))
                mstore(/** @src 9:1154:1181  "hex\"600b380380600b5f395ff3\"" */ add(/** @src 9:1423:1624  "abi.encodePacked(..." */ expr_mpos_3, /** @src 9:1154:1181  "hex\"600b380380600b5f395ff3\"" */ 53), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0)
                mstore(/** @src 9:1154:1181  "hex\"600b380380600b5f395ff3\"" */ add(/** @src 9:1423:1624  "abi.encodePacked(..." */ expr_mpos_3, /** @src 9:1154:1181  "hex\"600b380380600b5f395ff3\"" */ 85), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ expr)
                /// @src 9:1423:1624  "abi.encodePacked(..."
                mstore(expr_mpos_3, /** @src 9:1154:1181  "hex\"600b380380600b5f395ff3\"" */ 85)
                /// @src 9:1423:1624  "abi.encodePacked(..."
                finalize_allocation(expr_mpos_3, 117)
                /// @src 9:1393:1634  "return keccak256(..."
                let var_1 := /** @src 9:1400:1634  "keccak256(..." */ keccak256(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _10, mload(/** @src 9:1400:1634  "keccak256(..." */ expr_mpos_3))
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                mstore(0, var_1)
                mstore(/** @src 9:1486:1501  "market.midnight" */ 32, /** @src 9:1154:1181  "hex\"600b380380600b5f395ff3\"" */ 1)
                /// @src 0:43348:45641  "if (marketState[id].tickSpacing == 0) {..."
                if /** @src 0:43352:43384  "marketState[id].tickSpacing == 0" */ iszero(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(shr(144, sload(/** @src 0:43352:43379  "marketState[id].tickSpacing" */ add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ keccak256(0, 64), /** @src 0:43352:43379  "marketState[id].tickSpacing" */ 2))), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xff))
                /// @src 0:43348:45641  "if (marketState[id].tickSpacing == 0) {..."
                {
                    /// @src 7:234:238  "1e36"
                    let _11 := mload(/** @src 0:43408:43422  "market.chainId" */ var_market_2995_mpos)
                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                    if iszero(/** @src 0:43408:43439  "market.chainId == block.chainid" */ eq(_11, /** @src 0:43426:43439  "block.chainid" */ chainid()))
                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                    {
                        mstore(0, shl(225, 0x3d23e4d1))
                        revert(0, 4)
                    }
                    let cleaned := and(mload(/** @src 0:43480:43495  "market.midnight" */ _1), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff)
                    if iszero(/** @src 0:43480:43512  "market.midnight == address(this)" */ eq(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ cleaned, /** @src 0:43507:43511  "this" */ address()))
                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                    {
                        mstore(0, shl(228, 0x06e25f05))
                        revert(0, 4)
                    }
                    /// @src 7:234:238  "1e36"
                    let _12 := mload(/** @src 0:43554:43569  "market.maturity" */ add(var_market_2995_mpos, 128))
                    /// @src 7:892:894  "16"
                    let sum := add(/** @src 0:43573:43588  "block.timestamp" */ timestamp(), /** @src 0:43591:43605  "100 * 365 days" */ 0xbbf81e00)
                    /// @src 7:892:894  "16"
                    if gt(/** @src 0:43573:43588  "block.timestamp" */ timestamp(), /** @src 7:892:894  "16" */ sum)
                    {
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(0, shl(224, 0x4e487b71))
                        mstore(4, 0x11)
                        revert(0, 0x24)
                    }
                    if /** @src 0:43554:43605  "market.maturity <= block.timestamp + 100 * 365 days" */ gt(_12, sum)
                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                    {
                        mstore(0, shl(224, 0x23dcaa73))
                        revert(0, 4)
                    }
                    /// @src 0:43646:43669  "market.collateralParams"
                    let _13 := add(var_market_2995_mpos, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 96)
                    if /** @src 0:43646:43680  "market.collateralParams.length > 0" */ iszero(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(/** @src 0:43646:43669  "market.collateralParams" */ mload(_13)))
                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                    {
                        mstore(0, shl(224, 0x4c000347))
                        revert(0, 4)
                    }
                    /// @src 7:839:842  "128"
                    if /** @src 0:43725:43774  "market.collateralParams.length <= MAX_COLLATERALS" */ gt(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(/** @src 0:43725:43748  "market.collateralParams" */ mload(_13)), /** @src 0:43554:43569  "market.maturity" */ 128)
                    /// @src 7:839:842  "128"
                    {
                        mstore(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0, /** @src 7:839:842  "128" */ shl(225, 0x74131f01))
                        revert(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0, /** @src 7:839:842  "128" */ 4)
                    }
                    /// @src 0:43816:43847  "address previousCollateralToken"
                    let var_previousCollateralToken := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                    /// @src 0:43816:43847  "address previousCollateralToken"
                    var_previousCollateralToken := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                    /// @src 0:43866:43879  "uint256 i = 0"
                    let var_i := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                    /// @src 0:43861:44713  "for (uint256 i = 0; i < market.collateralParams.length; i++) {..."
                    for { }
                    /** @src 9:1154:1181  "hex\"600b380380600b5f395ff3\"" */ 1
                    /// @src 0:43866:43879  "uint256 i = 0"
                    {
                        /// @src 0:43917:43920  "i++"
                        var_i := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ add(/** @src 0:43917:43920  "i++" */ var_i, /** @src 9:1154:1181  "hex\"600b380380600b5f395ff3\"" */ 1)
                    }
                    /// @src 0:43917:43920  "i++"
                    {
                        /// @src 0:43885:43908  "market.collateralParams"
                        let _1273_mpos := mload(_13)
                        /// @src 0:43881:43915  "i < market.collateralParams.length"
                        if iszero(lt(var_i, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(/** @src 0:43885:43915  "market.collateralParams.length" */ _1273_mpos)))
                        /// @src 0:43881:43915  "i < market.collateralParams.length"
                        { break }
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let cleaned_1 := and(mload(/** @src 0:43966:43992  "market.collateralParams[i]" */ mload(memory_array_index_access_struct_CollateralParams_dyn(_1273_mpos, var_i))), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff)
                        /// @src 7:839:842  "128"
                        if iszero(/** @src 0:44024:44065  "collateralToken > previousCollateralToken" */ gt(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ cleaned_1, and(/** @src 0:44024:44065  "collateralToken > previousCollateralToken" */ var_previousCollateralToken, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff)))
                        /// @src 7:839:842  "128"
                        {
                            mstore(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0, /** @src 7:839:842  "128" */ shl(224, 0xb673f32b))
                            revert(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0, /** @src 7:839:842  "128" */ 4)
                        }
                        /// @src 7:234:238  "1e36"
                        let _14 := mload(/** @src 0:44128:44159  "market.collateralParams[i].lltv" */ add(/** @src 0:44128:44154  "market.collateralParams[i]" */ mload(memory_array_index_access_struct_CollateralParams_dyn(/** @src 0:44128:44151  "market.collateralParams" */ mload(_13), /** @src 0:44128:44154  "market.collateralParams[i]" */ var_i)), /** @src 9:1486:1501  "market.midnight" */ 32))
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        mstore(0, _14)
                        mstore(/** @src 9:1486:1501  "market.midnight" */ 32, /** @src 0:44185:44198  "isLltvEnabled" */ 0x07)
                        /// @src 7:839:842  "128"
                        if iszero(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(sload(keccak256(0, 64)), 0xff))
                        /// @src 7:839:842  "128"
                        {
                            mstore(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0, /** @src 7:839:842  "128" */ shl(230, 0x01872dff))
                            revert(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0, /** @src 7:839:842  "128" */ 4)
                        }
                        /// @src 7:234:238  "1e36"
                        let _15 := mload(/** @src 0:44269:44313  "market.collateralParams[i].liquidationCursor" */ add(/** @src 0:44269:44295  "market.collateralParams[i]" */ mload(memory_array_index_access_struct_CollateralParams_dyn(/** @src 0:44269:44292  "market.collateralParams" */ mload(_13), /** @src 0:44269:44295  "market.collateralParams[i]" */ var_i)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 64))
                        mstore(0, _15)
                        mstore(/** @src 9:1486:1501  "market.midnight" */ 32, /** @src 0:44339:44365  "isLiquidationCursorEnabled" */ 0x08)
                        /// @src 7:839:842  "128"
                        if iszero(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(sload(keccak256(0, 64)), 0xff))
                        /// @src 7:839:842  "128"
                        {
                            mstore(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0, /** @src 7:839:842  "128" */ shl(224, 0x2f4a1643))
                            revert(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0, /** @src 7:839:842  "128" */ 4)
                        }
                        /// @src 0:44452:44483  "maxLif(lltv, liquidationCursor)"
                        let expr_1 := fun_maxLif(_14, _15)
                        /// @src 7:839:842  "128"
                        if /** @src 0:44509:44527  "_maxLif <= 2 * WAD" */ gt(expr_1, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x1bc16d674ec80000)
                        /// @src 7:839:842  "128"
                        {
                            mstore(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0, /** @src 7:839:842  "128" */ shl(224, 0xb8cd9f1d))
                            revert(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0, /** @src 7:839:842  "128" */ 4)
                        }
                        /// @src 0:44571:44621  "lltv == WAD || lltv * _maxLif <= 0.999 ether * WAD"
                        let expr_2 := /** @src 0:44571:44582  "lltv == WAD" */ eq(_14, /** @src 7:190:194  "1e18" */ 0x0de0b6b3a7640000)
                        /// @src 0:44571:44621  "lltv == WAD || lltv * _maxLif <= 0.999 ether * WAD"
                        if iszero(expr_2)
                        {
                            expr_2 := /** @src 0:44586:44621  "lltv * _maxLif <= 0.999 ether * WAD" */ iszero(gt(/** @src 0:44586:44600  "lltv * _maxLif" */ checked_mul_uint256(_14, expr_1), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xc06680b58479827a8a440600000000))
                        }
                        /// @src 7:839:842  "128"
                        if iszero(expr_2)
                        {
                            mstore(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0, /** @src 7:839:842  "128" */ shl(226, 0x22b6453b))
                            revert(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0, /** @src 7:839:842  "128" */ 4)
                        }
                        /// @src 0:44657:44698  "previousCollateralToken = collateralToken"
                        var_previousCollateralToken := cleaned_1
                    }
                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                    mstore(0, var_1)
                    mstore(/** @src 9:1486:1501  "market.midnight" */ 32, /** @src 9:1154:1181  "hex\"600b380380600b5f395ff3\"" */ 1)
                    /// @src 0:44791:44815  "_marketState.tickSpacing"
                    let _16 := add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ keccak256(0, 64), /** @src 0:43352:43379  "marketState[id].tickSpacing" */ 2)
                    /// @src 7:1114:1115  "4"
                    sstore(_16, or(and(sload(_16), not(shl(144, /** @src 7:190:194  "1e18" */ 255))), /** @src 7:1114:1115  "4" */ shl(146, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 1)))
                    /// @src 0:44920:44936  "market.loanToken"
                    let _17 := add(var_market_2995_mpos, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 64)
                    mstore(0, and(mload(/** @src 0:44920:44936  "market.loanToken" */ _17), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                    mstore(/** @src 9:1486:1501  "market.midnight" */ 32, /** @src 7:1114:1115  "4" */ 0x04)
                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                    let dataSlot := keccak256(0, 64)
                    /// @src 7:1114:1115  "4"
                    let memPtr := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                    /// @src 7:1114:1115  "4"
                    let data := sload(dataSlot)
                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                    mstore(memPtr, and(/** @src 7:1114:1115  "4" */ data, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffff))
                    /// @src 7:1114:1115  "4"
                    let _18 := add(memPtr, /** @src 9:1486:1501  "market.midnight" */ 32)
                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                    mstore(_18, and(shr(16, /** @src 7:1114:1115  "4" */ data), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffff))
                    /// @src 7:1114:1115  "4"
                    let _19 := add(memPtr, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 64)
                    mstore(_19, and(shr(/** @src 9:1486:1501  "market.midnight" */ 32, /** @src 7:1114:1115  "4" */ data), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffff))
                    /// @src 7:1114:1115  "4"
                    let _20 := add(memPtr, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 96)
                    mstore(_20, and(shr(48, /** @src 7:1114:1115  "4" */ data), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffff))
                    /// @src 7:1114:1115  "4"
                    let _21 := add(memPtr, /** @src 0:43554:43569  "market.maturity" */ 128)
                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                    mstore(_21, and(shr(64, /** @src 7:1114:1115  "4" */ data), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffff))
                    /// @src 7:1114:1115  "4"
                    let _22 := add(memPtr, 160)
                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                    mstore(_22, and(shr(80, /** @src 7:1114:1115  "4" */ data), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffff))
                    /// @src 7:1114:1115  "4"
                    let _23 := add(memPtr, 192)
                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                    mstore(_23, and(shr(96, /** @src 7:1114:1115  "4" */ data), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffff))
                    /// @src 7:1114:1115  "4"
                    finalize_allocation(memPtr, 0xe0)
                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                    sstore(/** @src 0:44951:45011  "_marketState.settlementFeeCbp0 = _defaultSettlementFeeCbp[0]" */ _16, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ or(and(sload(/** @src 0:44951:45011  "_marketState.settlementFeeCbp0 = _defaultSettlementFeeCbp[0]" */ _16), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(65535)), and(and(/** @src 7:1114:1115  "4" */ mload(memPtr), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffff), 0xffff)))
                    /// @src 0:45025:45085  "_marketState.settlementFeeCbp1 = _defaultSettlementFeeCbp[1]"
                    update_storage_value_offset_2_uint16_to_uint16(_16, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 7:1114:1115  "4" */ mload(_18), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffff))
                    /// @src 0:45099:45159  "_marketState.settlementFeeCbp2 = _defaultSettlementFeeCbp[2]"
                    update_storage_value_offset_4_uint16_to_uint16(_16, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 7:1114:1115  "4" */ mload(_19), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffff))
                    /// @src 0:45173:45233  "_marketState.settlementFeeCbp3 = _defaultSettlementFeeCbp[3]"
                    update_storage_value_offset_t_uint16_to_t_uint16(_16, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 7:1114:1115  "4" */ mload(_20), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffff))
                    /// @src 0:45247:45307  "_marketState.settlementFeeCbp4 = _defaultSettlementFeeCbp[4]"
                    update_storage_value_offset_8_uint16_to_uint16(_16, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 7:1114:1115  "4" */ mload(_21), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffff))
                    /// @src 0:45321:45381  "_marketState.settlementFeeCbp5 = _defaultSettlementFeeCbp[5]"
                    update_storage_value_offset_uint16_to_uint16(_16, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 7:1114:1115  "4" */ mload(_22), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffff))
                    /// @src 0:45395:45455  "_marketState.settlementFeeCbp6 = _defaultSettlementFeeCbp[6]"
                    update_storage_value_offset_12_uint16_to_uint16(_16, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 7:1114:1115  "4" */ mload(_23), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffff))
                    mstore(0, and(mload(/** @src 0:45519:45535  "market.loanToken" */ _17), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                    mstore(/** @src 9:1486:1501  "market.midnight" */ 32, /** @src 7:1114:1115  "4" */ 5)
                    /// @src 0:45469:45536  "_marketState.continuousFee = defaultContinuousFee[market.loanToken]"
                    update_storage_value_offset_uint32_to_uint32(_16, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 7:1114:1115  "4" */ sload(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ keccak256(0, 64)), 0xffffffff))
                    /// @src 9:2026:2040  "SSTORE2_PREFIX"
                    let expr_mpos_4 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ copy_literal_to_memory_a55ffd6cc2b0b507f8827f3c680fa2adb9285b64bf7fb098798ce57c2156693f()
                    /// @src 9:2042:2060  "abi.encode(market)"
                    let expr_mpos_5 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                    /// @src 9:2042:2060  "abi.encode(market)"
                    let _24 := add(expr_mpos_5, /** @src 9:1486:1501  "market.midnight" */ 32)
                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                    mstore(_24, /** @src 9:1486:1501  "market.midnight" */ 32)
                    /// @src 9:2042:2060  "abi.encode(market)"
                    let _25 := sub(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ abi_encode_struct_Market(var_market_2995_mpos, add(/** @src 9:2042:2060  "abi.encode(market)" */ expr_mpos_5, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 64)), /** @src 9:2042:2060  "abi.encode(market)" */ expr_mpos_5)
                    mstore(expr_mpos_5, add(_25, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(31)))
                    /// @src 9:2042:2060  "abi.encode(market)"
                    finalize_allocation(expr_mpos_5, _25)
                    /// @src 9:2009:2061  "abi.encodePacked(SSTORE2_PREFIX, abi.encode(market))"
                    let expr_mpos_6 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                    /// @src 9:2009:2061  "abi.encodePacked(SSTORE2_PREFIX, abi.encode(market))"
                    let _26 := add(expr_mpos_6, /** @src 9:1486:1501  "market.midnight" */ 32)
                    /// @src 9:1154:1181  "hex\"600b380380600b5f395ff3\""
                    let length_2 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(/** @src 9:1154:1181  "hex\"600b380380600b5f395ff3\"" */ expr_mpos_4)
                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                    mcopy(_26, /** @src 9:1154:1181  "hex\"600b380380600b5f395ff3\"" */ add(expr_mpos_4, /** @src 9:1486:1501  "market.midnight" */ 32), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ length_2)
                    let _27 := add(/** @src 9:2009:2061  "abi.encodePacked(SSTORE2_PREFIX, abi.encode(market))" */ expr_mpos_6, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ length_2)
                    let _28 := add(_27, /** @src 9:1486:1501  "market.midnight" */ 32)
                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                    mstore(_28, 0)
                    /// @src 9:1154:1181  "hex\"600b380380600b5f395ff3\""
                    let length_3 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(/** @src 9:1154:1181  "hex\"600b380380600b5f395ff3\"" */ expr_mpos_5)
                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                    mcopy(_28, _24, length_3)
                    let _29 := add(add(_27, length_3), /** @src 9:1486:1501  "market.midnight" */ 32)
                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                    mstore(_29, 0)
                    /// @src 9:2009:2061  "abi.encodePacked(SSTORE2_PREFIX, abi.encode(market))"
                    let _30 := sub(_29, expr_mpos_6)
                    mstore(expr_mpos_6, add(_30, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(31)))
                    /// @src 9:2009:2061  "abi.encodePacked(SSTORE2_PREFIX, abi.encode(market))"
                    finalize_allocation(expr_mpos_6, _30)
                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                    if /** @src 9:2214:2242  "create2Address != address(0)" */ iszero(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 9:2071:2197  "assembly (\"memory-safe\") {..." */ create2(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0, /** @src 9:2071:2197  "assembly (\"memory-safe\") {..." */ _26, mload(expr_mpos_6), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0), 0xffffffffffffffffffffffffffffffffffffffff))
                    {
                        mstore(0, shl(225, 0x41b2ccbf))
                        revert(0, /** @src 7:1114:1115  "4" */ 0x04)
                    }
                    /// @src 0:45595:45630  "EventsLib.MarketCreated(market, id)"
                    let _31 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                    mstore(_31, /** @src 9:1486:1501  "market.midnight" */ 32)
                    /// @src 0:45595:45630  "EventsLib.MarketCreated(market, id)"
                    log2(_31, sub(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ abi_encode_struct_Market(var_market_2995_mpos, add(_31, /** @src 9:1486:1501  "market.midnight" */ 32)), /** @src 0:45595:45630  "EventsLib.MarketCreated(market, id)" */ _31), 0xdbf3e95a2290945645820c722294f678e0b3522a7dcf3cf2e2870268bf6c9472, var_1)
                }
                /// @src 0:45650:45659  "return id"
                var := var_1
            }
            /// @ast-id 3806 @src 0:50023:51416  "function settlementFee(bytes32 id, uint256 timeToMaturity) public view returns (uint256) {..."
            function fun_settlementFee(var_id, var_timeToMaturity) -> var
            {
                /// @src 0:50103:50110  "uint256"
                var := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                mstore(0, var_id)
                mstore(0x20, /** @src 0:50157:50168  "marketState" */ 0x01)
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                let _1 := sload(/** @src 0:50190:50214  "_marketState.tickSpacing" */ add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ keccak256(0, 0x40), /** @src 0:50190:50214  "_marketState.tickSpacing" */ 2))
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                if /** @src 0:50190:50218  "_marketState.tickSpacing > 0" */ iszero(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(shr(144, _1), 0xff))
                {
                    mstore(0, shl(224, 0x96e13529))
                    revert(0, 4)
                }
                /// @src 0:50250:50325  "if (timeToMaturity >= 360 days) return _marketState.settlementFeeCbp6 * CBP"
                if /** @src 0:50254:50280  "timeToMaturity >= 360 days" */ iszero(lt(var_timeToMaturity, /** @src 0:50272:50280  "360 days" */ 0x01da9c00))
                /// @src 0:50250:50325  "if (timeToMaturity >= 360 days) return _marketState.settlementFeeCbp6 * CBP"
                {
                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                    let value := and(shr(96, _1), 0xffff)
                    let product := mul(value, /** @src 7:263:267  "1e12" */ 0xe8d4a51000)
                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                    if iszero(or(iszero(value), eq(/** @src 7:263:267  "1e12" */ 0xe8d4a51000, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ div(product, value))))
                    {
                        mstore(0, shl(224, 0x4e487b71))
                        mstore(4, 0x11)
                        revert(0, 0x24)
                    }
                    /// @src 0:50282:50325  "return _marketState.settlementFeeCbp6 * CBP"
                    var := product
                    leave
                }
                /// @src 0:50450:51269  "timeToMaturity < 1 days   ? (  0 days,   1 days, _marketState.settlementFeeCbp0 * CBP, _marketState.settlementFeeCbp1 * CBP) :..."
                let expr_3783_component := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                let expr_3783_component_1 := 0
                let expr_3783_component_2 := 0
                let expr_3783_component_3 := 0
                /// @src 0:50450:51269  "timeToMaturity < 1 days   ? (  0 days,   1 days, _marketState.settlementFeeCbp0 * CBP, _marketState.settlementFeeCbp1 * CBP) :..."
                switch /** @src 0:50450:50473  "timeToMaturity < 1 days" */ lt(var_timeToMaturity, /** @src 0:50467:50473  "1 days" */ 0x015180)
                case /** @src 0:50450:51269  "timeToMaturity < 1 days   ? (  0 days,   1 days, _marketState.settlementFeeCbp0 * CBP, _marketState.settlementFeeCbp1 * CBP) :..." */ 0 {
                    /// @src 0:50589:51269  "timeToMaturity < 7 days   ? (  1 days,   7 days, _marketState.settlementFeeCbp1 * CBP, _marketState.settlementFeeCbp2 * CBP) :..."
                    let expr_3782_component := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                    let expr_3782_component_1 := 0
                    let expr_3782_component_2 := 0
                    let expr_3782_component_3 := 0
                    /// @src 0:50589:51269  "timeToMaturity < 7 days   ? (  1 days,   7 days, _marketState.settlementFeeCbp1 * CBP, _marketState.settlementFeeCbp2 * CBP) :..."
                    switch /** @src 0:50589:50612  "timeToMaturity < 7 days" */ lt(var_timeToMaturity, /** @src 0:50606:50612  "7 days" */ 0x093a80)
                    case /** @src 0:50589:51269  "timeToMaturity < 7 days   ? (  1 days,   7 days, _marketState.settlementFeeCbp1 * CBP, _marketState.settlementFeeCbp2 * CBP) :..." */ 0 {
                        /// @src 0:50728:51269  "timeToMaturity < 30 days  ? (  7 days,  30 days, _marketState.settlementFeeCbp2 * CBP, _marketState.settlementFeeCbp3 * CBP) :..."
                        let expr_3781_component := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                        let expr_3781_component_1 := 0
                        let expr_3781_component_2 := 0
                        let expr_3781_component_3 := 0
                        /// @src 0:50728:51269  "timeToMaturity < 30 days  ? (  7 days,  30 days, _marketState.settlementFeeCbp2 * CBP, _marketState.settlementFeeCbp3 * CBP) :..."
                        switch /** @src 0:50728:50752  "timeToMaturity < 30 days" */ lt(var_timeToMaturity, /** @src 0:50745:50752  "30 days" */ 0x278d00)
                        case /** @src 0:50728:51269  "timeToMaturity < 30 days  ? (  7 days,  30 days, _marketState.settlementFeeCbp2 * CBP, _marketState.settlementFeeCbp3 * CBP) :..." */ 0 {
                            /// @src 0:50867:51269  "timeToMaturity < 90 days  ? ( 30 days,  90 days, _marketState.settlementFeeCbp3 * CBP, _marketState.settlementFeeCbp4 * CBP) :..."
                            let expr_component := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                            let expr_3780_component := 0
                            let expr_3780_component_1 := 0
                            let expr_3780_component_2 := 0
                            /// @src 0:50867:51269  "timeToMaturity < 90 days  ? ( 30 days,  90 days, _marketState.settlementFeeCbp3 * CBP, _marketState.settlementFeeCbp4 * CBP) :..."
                            switch /** @src 0:50867:50891  "timeToMaturity < 90 days" */ lt(var_timeToMaturity, /** @src 0:50884:50891  "90 days" */ 0x76a700)
                            case /** @src 0:50867:51269  "timeToMaturity < 90 days  ? ( 30 days,  90 days, _marketState.settlementFeeCbp3 * CBP, _marketState.settlementFeeCbp4 * CBP) :..." */ 0 {
                                /// @src 0:51006:51269  "timeToMaturity < 180 days ? ( 90 days, 180 days, _marketState.settlementFeeCbp4 * CBP, _marketState.settlementFeeCbp5 * CBP) :..."
                                let expr_component_1 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                                let expr_component_2 := 0
                                let expr_component_3 := 0
                                let expr_component_4 := 0
                                /// @src 0:51006:51269  "timeToMaturity < 180 days ? ( 90 days, 180 days, _marketState.settlementFeeCbp4 * CBP, _marketState.settlementFeeCbp5 * CBP) :..."
                                switch /** @src 0:51006:51031  "timeToMaturity < 180 days" */ lt(var_timeToMaturity, /** @src 0:51023:51031  "180 days" */ 0xed4e00)
                                case /** @src 0:51006:51269  "timeToMaturity < 180 days ? ( 90 days, 180 days, _marketState.settlementFeeCbp4 * CBP, _marketState.settlementFeeCbp5 * CBP) :..." */ 0 {
                                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                    let value_1 := and(shr(80, _1), 0xffff)
                                    let product_1 := mul(value_1, /** @src 7:263:267  "1e12" */ 0xe8d4a51000)
                                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                    if iszero(or(iszero(value_1), eq(/** @src 7:263:267  "1e12" */ 0xe8d4a51000, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ div(product_1, value_1))))
                                    {
                                        mstore(0, shl(224, 0x4e487b71))
                                        mstore(4, 0x11)
                                        revert(0, 0x24)
                                    }
                                    let value_2 := and(shr(96, _1), 0xffff)
                                    let product_2 := mul(value_2, /** @src 7:263:267  "1e12" */ 0xe8d4a51000)
                                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                    if iszero(or(iszero(value_2), eq(/** @src 7:263:267  "1e12" */ 0xe8d4a51000, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ div(product_2, value_2))))
                                    {
                                        mstore(0, shl(224, 0x4e487b71))
                                        mstore(4, 0x11)
                                        revert(0, 0x24)
                                    }
                                    /// @src 0:51006:51269  "timeToMaturity < 180 days ? ( 90 days, 180 days, _marketState.settlementFeeCbp4 * CBP, _marketState.settlementFeeCbp5 * CBP) :..."
                                    expr_component_1 := /** @src 0:51023:51031  "180 days" */ 0xed4e00
                                    /// @src 0:51006:51269  "timeToMaturity < 180 days ? ( 90 days, 180 days, _marketState.settlementFeeCbp4 * CBP, _marketState.settlementFeeCbp5 * CBP) :..."
                                    expr_component_2 := /** @src 0:50272:50280  "360 days" */ 0x01da9c00
                                    /// @src 0:51006:51269  "timeToMaturity < 180 days ? ( 90 days, 180 days, _marketState.settlementFeeCbp4 * CBP, _marketState.settlementFeeCbp5 * CBP) :..."
                                    expr_component_3 := product_1
                                    expr_component_4 := product_2
                                }
                                default {
                                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                    let value_3 := and(shr(0x40, _1), 0xffff)
                                    let product_3 := mul(value_3, /** @src 7:263:267  "1e12" */ 0xe8d4a51000)
                                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                    if iszero(or(iszero(value_3), eq(/** @src 7:263:267  "1e12" */ 0xe8d4a51000, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ div(product_3, value_3))))
                                    {
                                        mstore(0, shl(224, 0x4e487b71))
                                        mstore(4, 0x11)
                                        revert(0, 0x24)
                                    }
                                    let value_4 := and(shr(80, _1), 0xffff)
                                    let product_4 := mul(value_4, /** @src 7:263:267  "1e12" */ 0xe8d4a51000)
                                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                    if iszero(or(iszero(value_4), eq(/** @src 7:263:267  "1e12" */ 0xe8d4a51000, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ div(product_4, value_4))))
                                    {
                                        mstore(0, shl(224, 0x4e487b71))
                                        mstore(4, 0x11)
                                        revert(0, 0x24)
                                    }
                                    /// @src 0:51006:51269  "timeToMaturity < 180 days ? ( 90 days, 180 days, _marketState.settlementFeeCbp4 * CBP, _marketState.settlementFeeCbp5 * CBP) :..."
                                    expr_component_1 := /** @src 0:50884:50891  "90 days" */ 0x76a700
                                    /// @src 0:51006:51269  "timeToMaturity < 180 days ? ( 90 days, 180 days, _marketState.settlementFeeCbp4 * CBP, _marketState.settlementFeeCbp5 * CBP) :..."
                                    expr_component_2 := /** @src 0:51023:51031  "180 days" */ 0xed4e00
                                    /// @src 0:51006:51269  "timeToMaturity < 180 days ? ( 90 days, 180 days, _marketState.settlementFeeCbp4 * CBP, _marketState.settlementFeeCbp5 * CBP) :..."
                                    expr_component_3 := product_3
                                    expr_component_4 := product_4
                                }
                                /// @src 0:50867:51269  "timeToMaturity < 90 days  ? ( 30 days,  90 days, _marketState.settlementFeeCbp3 * CBP, _marketState.settlementFeeCbp4 * CBP) :..."
                                expr_component := expr_component_1
                                expr_3780_component := expr_component_2
                                expr_3780_component_1 := expr_component_3
                                expr_3780_component_2 := expr_component_4
                            }
                            default {
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                let value_5 := and(shr(48, _1), 0xffff)
                                let product_5 := mul(value_5, /** @src 7:263:267  "1e12" */ 0xe8d4a51000)
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                if iszero(or(iszero(value_5), eq(/** @src 7:263:267  "1e12" */ 0xe8d4a51000, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ div(product_5, value_5))))
                                {
                                    mstore(0, shl(224, 0x4e487b71))
                                    mstore(4, 0x11)
                                    revert(0, 0x24)
                                }
                                let value_6 := and(shr(0x40, _1), 0xffff)
                                let product_6 := mul(value_6, /** @src 7:263:267  "1e12" */ 0xe8d4a51000)
                                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                                if iszero(or(iszero(value_6), eq(/** @src 7:263:267  "1e12" */ 0xe8d4a51000, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ div(product_6, value_6))))
                                {
                                    mstore(0, shl(224, 0x4e487b71))
                                    mstore(4, 0x11)
                                    revert(0, 0x24)
                                }
                                /// @src 0:50867:51269  "timeToMaturity < 90 days  ? ( 30 days,  90 days, _marketState.settlementFeeCbp3 * CBP, _marketState.settlementFeeCbp4 * CBP) :..."
                                expr_component := /** @src 0:50745:50752  "30 days" */ 0x278d00
                                /// @src 0:50867:51269  "timeToMaturity < 90 days  ? ( 30 days,  90 days, _marketState.settlementFeeCbp3 * CBP, _marketState.settlementFeeCbp4 * CBP) :..."
                                expr_3780_component := /** @src 0:50884:50891  "90 days" */ 0x76a700
                                /// @src 0:50867:51269  "timeToMaturity < 90 days  ? ( 30 days,  90 days, _marketState.settlementFeeCbp3 * CBP, _marketState.settlementFeeCbp4 * CBP) :..."
                                expr_3780_component_1 := product_5
                                expr_3780_component_2 := product_6
                            }
                            /// @src 0:50728:51269  "timeToMaturity < 30 days  ? (  7 days,  30 days, _marketState.settlementFeeCbp2 * CBP, _marketState.settlementFeeCbp3 * CBP) :..."
                            expr_3781_component := expr_component
                            expr_3781_component_1 := expr_3780_component
                            expr_3781_component_2 := expr_3780_component_1
                            expr_3781_component_3 := expr_3780_component_2
                        }
                        default {
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            let value_7 := and(shr(0x20, _1), 0xffff)
                            let product_7 := mul(value_7, /** @src 7:263:267  "1e12" */ 0xe8d4a51000)
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            if iszero(or(iszero(value_7), eq(/** @src 7:263:267  "1e12" */ 0xe8d4a51000, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ div(product_7, value_7))))
                            {
                                mstore(0, shl(224, 0x4e487b71))
                                mstore(4, 0x11)
                                revert(0, 0x24)
                            }
                            let value_8 := and(shr(48, _1), 0xffff)
                            let product_8 := mul(value_8, /** @src 7:263:267  "1e12" */ 0xe8d4a51000)
                            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                            if iszero(or(iszero(value_8), eq(/** @src 7:263:267  "1e12" */ 0xe8d4a51000, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ div(product_8, value_8))))
                            {
                                mstore(0, shl(224, 0x4e487b71))
                                mstore(4, 0x11)
                                revert(0, 0x24)
                            }
                            /// @src 0:50728:51269  "timeToMaturity < 30 days  ? (  7 days,  30 days, _marketState.settlementFeeCbp2 * CBP, _marketState.settlementFeeCbp3 * CBP) :..."
                            expr_3781_component := /** @src 0:50606:50612  "7 days" */ 0x093a80
                            /// @src 0:50728:51269  "timeToMaturity < 30 days  ? (  7 days,  30 days, _marketState.settlementFeeCbp2 * CBP, _marketState.settlementFeeCbp3 * CBP) :..."
                            expr_3781_component_1 := /** @src 0:50745:50752  "30 days" */ 0x278d00
                            /// @src 0:50728:51269  "timeToMaturity < 30 days  ? (  7 days,  30 days, _marketState.settlementFeeCbp2 * CBP, _marketState.settlementFeeCbp3 * CBP) :..."
                            expr_3781_component_2 := product_7
                            expr_3781_component_3 := product_8
                        }
                        /// @src 0:50589:51269  "timeToMaturity < 7 days   ? (  1 days,   7 days, _marketState.settlementFeeCbp1 * CBP, _marketState.settlementFeeCbp2 * CBP) :..."
                        expr_3782_component := expr_3781_component
                        expr_3782_component_1 := expr_3781_component_1
                        expr_3782_component_2 := expr_3781_component_2
                        expr_3782_component_3 := expr_3781_component_3
                    }
                    default {
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        let value_9 := and(shr(16, _1), 0xffff)
                        let product_9 := mul(value_9, /** @src 7:263:267  "1e12" */ 0xe8d4a51000)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        if iszero(or(iszero(value_9), eq(/** @src 7:263:267  "1e12" */ 0xe8d4a51000, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ div(product_9, value_9))))
                        {
                            mstore(0, shl(224, 0x4e487b71))
                            mstore(4, 0x11)
                            revert(0, 0x24)
                        }
                        let value_10 := and(shr(0x20, _1), 0xffff)
                        let product_10 := mul(value_10, /** @src 7:263:267  "1e12" */ 0xe8d4a51000)
                        /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                        if iszero(or(iszero(value_10), eq(/** @src 7:263:267  "1e12" */ 0xe8d4a51000, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ div(product_10, value_10))))
                        {
                            mstore(0, shl(224, 0x4e487b71))
                            mstore(4, 0x11)
                            revert(0, 0x24)
                        }
                        /// @src 0:50589:51269  "timeToMaturity < 7 days   ? (  1 days,   7 days, _marketState.settlementFeeCbp1 * CBP, _marketState.settlementFeeCbp2 * CBP) :..."
                        expr_3782_component := /** @src 0:50467:50473  "1 days" */ 0x015180
                        /// @src 0:50589:51269  "timeToMaturity < 7 days   ? (  1 days,   7 days, _marketState.settlementFeeCbp1 * CBP, _marketState.settlementFeeCbp2 * CBP) :..."
                        expr_3782_component_1 := /** @src 0:50606:50612  "7 days" */ 0x093a80
                        /// @src 0:50589:51269  "timeToMaturity < 7 days   ? (  1 days,   7 days, _marketState.settlementFeeCbp1 * CBP, _marketState.settlementFeeCbp2 * CBP) :..."
                        expr_3782_component_2 := product_9
                        expr_3782_component_3 := product_10
                    }
                    /// @src 0:50450:51269  "timeToMaturity < 1 days   ? (  0 days,   1 days, _marketState.settlementFeeCbp0 * CBP, _marketState.settlementFeeCbp1 * CBP) :..."
                    expr_3783_component := expr_3782_component
                    expr_3783_component_1 := expr_3782_component_1
                    expr_3783_component_2 := expr_3782_component_2
                    expr_3783_component_3 := expr_3782_component_3
                }
                default {
                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                    let cleaned := and(_1, 0xffff)
                    let product_11 := mul(cleaned, /** @src 7:263:267  "1e12" */ 0xe8d4a51000)
                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                    if iszero(or(iszero(cleaned), eq(/** @src 7:263:267  "1e12" */ 0xe8d4a51000, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ div(product_11, cleaned))))
                    {
                        mstore(0, shl(224, 0x4e487b71))
                        mstore(4, 0x11)
                        revert(0, 0x24)
                    }
                    let value_11 := and(shr(16, _1), 0xffff)
                    let product_12 := mul(value_11, /** @src 7:263:267  "1e12" */ 0xe8d4a51000)
                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                    if iszero(or(iszero(value_11), eq(/** @src 7:263:267  "1e12" */ 0xe8d4a51000, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ div(product_12, value_11))))
                    {
                        mstore(0, shl(224, 0x4e487b71))
                        mstore(4, 0x11)
                        revert(0, 0x24)
                    }
                    /// @src 0:50450:51269  "timeToMaturity < 1 days   ? (  0 days,   1 days, _marketState.settlementFeeCbp0 * CBP, _marketState.settlementFeeCbp1 * CBP) :..."
                    expr_3783_component := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                    /// @src 0:50450:51269  "timeToMaturity < 1 days   ? (  0 days,   1 days, _marketState.settlementFeeCbp0 * CBP, _marketState.settlementFeeCbp1 * CBP) :..."
                    expr_3783_component_1 := /** @src 0:50467:50473  "1 days" */ 0x015180
                    /// @src 0:50450:51269  "timeToMaturity < 1 days   ? (  0 days,   1 days, _marketState.settlementFeeCbp0 * CBP, _marketState.settlementFeeCbp1 * CBP) :..."
                    expr_3783_component_2 := product_11
                    expr_3783_component_3 := product_12
                }
                /// @src 0:50371:51269  "(uint256 start, uint256 end, uint256 feeLower, uint256 feeUpper) =..."
                let var_start := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:50371:51269  "(uint256 start, uint256 end, uint256 feeLower, uint256 feeUpper) =..." */ expr_3783_component, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffff)
                /// @src 0:50371:51269  "(uint256 start, uint256 end, uint256 feeLower, uint256 feeUpper) =..."
                let var_end := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:50371:51269  "(uint256 start, uint256 end, uint256 feeLower, uint256 feeUpper) =..." */ expr_3783_component_1, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffff)
                /// @src 0:51321:51354  "feeLower * (end - timeToMaturity)"
                let expr := checked_mul_uint256(expr_3783_component_2, /** @src 0:51333:51353  "end - timeToMaturity" */ checked_sub_uint256(var_end, var_timeToMaturity))
                /// @src 0:51321:51392  "feeLower * (end - timeToMaturity) + feeUpper * (timeToMaturity - start)"
                let expr_1 := checked_add_uint256(expr, /** @src 0:51357:51392  "feeUpper * (timeToMaturity - start)" */ checked_mul_uint256(expr_3783_component_3, /** @src 0:51369:51391  "timeToMaturity - start" */ checked_sub_uint256(var_timeToMaturity, var_start)))
                /// @src 0:51313:51409  "return (feeLower * (end - timeToMaturity) + feeUpper * (timeToMaturity - start)) / (end - start)"
                var := /** @src 0:51320:51409  "(feeLower * (end - timeToMaturity) + feeUpper * (timeToMaturity - start)) / (end - start)" */ checked_div_uint256(expr_1, /** @src 0:51397:51408  "end - start" */ checked_sub_uint256(var_end, var_start))
            }
            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
            function extract_returndata() -> data
            {
                switch returndatasize()
                case 0 { data := 96 }
                default {
                    let _1 := returndatasize()
                    let _2 := array_allocation_size_bytes(_1)
                    let memPtr := mload(64)
                    finalize_allocation(memPtr, _2)
                    mstore(memPtr, _1)
                    data := memPtr
                    returndatacopy(add(memPtr, 0x20), /** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ returndatasize())
                }
            }
            /// @ast-id 3421 @src 0:45868:47220  "function updatePositionView(Market memory market, bytes32 id, address user)..."
            function fun_updatePositionView(var_market_mpos, var_id, var_user) -> var, var_1, var_2
            {
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                mstore(/** @src 0:46059:46067  "position" */ 0x00, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ var_id)
                mstore(0x20, /** @src 0:46059:46067  "position" */ 0x00)
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                let dataSlot := keccak256(/** @src 0:46059:46067  "position" */ 0x00, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x40)
                /// @src 0:46059:46077  "position[id][user]"
                let dataSlot_1 := /** @src -1:-1:-1 */ 0
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:46059:46077  "position[id][user]" */ var_user, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                mstore(0x20, /** @src 0:46059:46071  "position[id]" */ dataSlot)
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                dataSlot_1 := keccak256(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x40)
                let _1 := sload(/** @src 0:46059:46077  "position[id][user]" */ dataSlot_1)
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                let cleaned := and(_1, 0xffffffffffffffffffffffffffffffff)
                let _2 := sload(/** @src 0:46157:46181  "_position.lastLossFactor" */ add(/** @src 0:46059:46077  "position[id][user]" */ dataSlot_1, /** @src 0:46157:46181  "_position.lastLossFactor" */ 1))
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                let cleaned_1 := and(_2, 0xffffffffffffffffffffffffffffffff)
                /// @src 0:46217:46386  "_lastLossFactor < type(uint128).max..."
                let expr := /** @src 0:46059:46067  "position" */ 0x00
                /// @src 0:46217:46386  "_lastLossFactor < type(uint128).max..."
                switch /** @src 0:46217:46252  "_lastLossFactor < type(uint128).max" */ lt(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ cleaned_1, 0xffffffffffffffffffffffffffffffff)
                case /** @src 0:46217:46386  "_lastLossFactor < type(uint128).max..." */ 0 {
                    expr := /** @src 0:46059:46067  "position" */ 0x00
                }
                default /// @src 0:46217:46386  "_lastLossFactor < type(uint128).max..."
                {
                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                    mstore(/** @src 0:46059:46067  "position" */ 0x00, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ var_id)
                    mstore(0x20, /** @src 0:46157:46181  "_position.lastLossFactor" */ 1)
                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                    let diff := sub(0xffffffffffffffffffffffffffffffff, shr(128, sload(keccak256(/** @src 0:46059:46067  "position" */ 0x00, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x40))))
                    if gt(diff, 0xffffffffffffffffffffffffffffffff)
                    {
                        mstore(/** @src 0:46059:46067  "position" */ 0x00, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(224, 0x4e487b71))
                        mstore(4, 0x11)
                        revert(/** @src 0:46059:46067  "position" */ 0x00, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x24)
                    }
                    let diff_1 := sub(0xffffffffffffffffffffffffffffffff, cleaned_1)
                    if gt(diff_1, 0xffffffffffffffffffffffffffffffff)
                    {
                        mstore(/** @src 0:46059:46067  "position" */ 0x00, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(224, 0x4e487b71))
                        mstore(4, 0x11)
                        revert(/** @src 0:46059:46067  "position" */ 0x00, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x24)
                    }
                    /// @src 0:46217:46386  "_lastLossFactor < type(uint128).max..."
                    expr := /** @src 12:652:663  "(x * y) / d" */ checked_div_uint256(/** @src 12:653:658  "x * y" */ checked_mul_uint256(/** @src 0:46267:46370  "_credit.mulDivDown(type(uint128).max - marketState[id].lossFactor, type(uint128).max - _lastLossFactor)" */ cleaned, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:46267:46370  "_credit.mulDivDown(type(uint128).max - marketState[id].lossFactor, type(uint128).max - _lastLossFactor)" */ diff, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)), and(/** @src 0:46267:46370  "_credit.mulDivDown(type(uint128).max - marketState[id].lossFactor, type(uint128).max - _lastLossFactor)" */ diff_1, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff))
                }
                let _3 := shr(128, _1)
                /// @src 0:46490:46578  "_credit > 0 ? _pendingFee - _pendingFee.mulDivUp(_credit - postSlashCredit, _credit) : 0"
                let expr_1 := /** @src 0:46059:46067  "position" */ 0x00
                /// @src 0:46490:46578  "_credit > 0 ? _pendingFee - _pendingFee.mulDivUp(_credit - postSlashCredit, _credit) : 0"
                switch /** @src 0:46490:46501  "_credit > 0" */ iszero(iszero(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ cleaned))
                case /** @src 0:46490:46578  "_credit > 0 ? _pendingFee - _pendingFee.mulDivUp(_credit - postSlashCredit, _credit) : 0" */ 0 {
                    expr_1 := /** @src 0:46059:46067  "position" */ 0x00
                }
                default /// @src 0:46490:46578  "_credit > 0 ? _pendingFee - _pendingFee.mulDivUp(_credit - postSlashCredit, _credit) : 0"
                {
                    expr_1 := /** @src 0:46504:46574  "_pendingFee - _pendingFee.mulDivUp(_credit - postSlashCredit, _credit)" */ checked_sub_uint256(_3, /** @src 0:46518:46574  "_pendingFee.mulDivUp(_credit - postSlashCredit, _credit)" */ fun_mulDivUp(_3, /** @src 0:46539:46564  "_credit - postSlashCredit" */ checked_sub_uint256(cleaned, expr), /** @src 0:46518:46574  "_pendingFee.mulDivUp(_credit - postSlashCredit, _credit)" */ cleaned))
                }
                /// @src 0:46639:46654  "market.maturity"
                let _4 := add(var_market_mpos, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 128)
                /// @src 7:234:238  "1e36"
                let _5 := mload(/** @src 0:46639:46654  "market.maturity" */ _4)
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                let _6 := shr(128, _2)
                /// @src 0:46853:47012  "_lastAccrual < market.maturity..."
                let expr_2 := /** @src 0:46059:46067  "position" */ 0x00
                /// @src 0:46853:47012  "_lastAccrual < market.maturity..."
                switch /** @src 0:46853:46883  "_lastAccrual < market.maturity" */ lt(_6, _5)
                case /** @src 0:46853:47012  "_lastAccrual < market.maturity..." */ 0 {
                    expr_2 := /** @src 0:46059:46067  "position" */ 0x00
                }
                default /// @src 0:46853:47012  "_lastAccrual < market.maturity..."
                {
                    /// @src 0:46937:46962  "accrualEnd - _lastAccrual"
                    let expr_3 := checked_sub_uint256(/** @src 12:259:329  "assembly {..." */ xor(/** @src 0:46622:46637  "block.timestamp" */ timestamp(), /** @src 12:259:329  "assembly {..." */ mul(xor(/** @src 0:46622:46637  "block.timestamp" */ timestamp(), /** @src 12:259:329  "assembly {..." */ _5), lt(_5, /** @src 0:46622:46637  "block.timestamp" */ timestamp()))), /** @src 0:46937:46962  "accrualEnd - _lastAccrual" */ _6)
                    /// @src 0:46853:47012  "_lastAccrual < market.maturity..."
                    expr_2 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 12:652:663  "(x * y) / d" */ checked_div_uint256(/** @src 12:653:658  "x * y" */ checked_mul_uint256(expr_1, expr_3), /** @src 0:46964:46994  "market.maturity - _lastAccrual" */ checked_sub_uint256(/** @src 7:234:238  "1e36" */ mload(/** @src 0:46964:46979  "market.maturity" */ _4), /** @src 0:46964:46994  "market.maturity - _lastAccrual" */ _6)), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)
                }
                /// @src 0:47141:47171  "uint128(postSlashCredit) - fee"
                let expr_4 := checked_sub_uint128(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:47141:47165  "uint128(postSlashCredit)" */ expr, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff), /** @src 0:47141:47171  "uint128(postSlashCredit) - fee" */ expr_2)
                /// @src 0:47173:47207  "uint128(postSlashPendingFee) - fee"
                let expr_5 := checked_sub_uint128(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:47173:47201  "uint128(postSlashPendingFee)" */ expr_1, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff), /** @src 0:47173:47207  "uint128(postSlashPendingFee) - fee" */ expr_2)
                /// @src 0:47133:47213  "return (uint128(postSlashCredit) - fee, uint128(postSlashPendingFee) - fee, fee)"
                var := expr_4
                var_1 := expr_5
                var_2 := expr_2
            }
            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
            function abi_decode_address_fromMemory(offset) -> value
            {
                value := mload(offset)
                if iszero(eq(value, and(value, 0xffffffffffffffffffffffffffffffffffffffff))) { revert(0, 0) }
            }
            /// @ast-id 6185 @src 12:2750:3007  "function tGet(uint256 baseSlot, bytes32 key1, address key2) internal view returns (bool value) {..."
            function fun_tGet(var_key1, var_key2) -> var_value
            {
                /// @src 12:2888:2920  "abi.encode(key1, key2, baseSlot)"
                let expr_mpos := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                /// @src 12:2888:2920  "abi.encode(key1, key2, baseSlot)"
                let _1 := add(expr_mpos, 0x20)
                let tail := /** @src -1:-1:-1 */ 0
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                tail := add(/** @src 12:2888:2920  "abi.encode(key1, key2, baseSlot)" */ expr_mpos, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 128)
                mstore(_1, var_key1)
                mstore(add(/** @src 12:2888:2920  "abi.encode(key1, key2, baseSlot)" */ expr_mpos, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 64), and(var_key2, 0xffffffffffffffffffffffffffffffffffffffff))
                mstore(add(/** @src 12:2888:2920  "abi.encode(key1, key2, baseSlot)" */ expr_mpos, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 96), /** @src 7:945:991  "keccak256(\"morpho.midnight.liquidationLocked\")" */ 0x90e10dad8320b2f9ee6b84bebe89829c27a3fc1209e68031bc1d4b65c22e4da4)
                /// @src 12:2888:2920  "abi.encode(key1, key2, baseSlot)"
                mstore(expr_mpos, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 96)
                /// @src 12:2888:2920  "abi.encode(key1, key2, baseSlot)"
                finalize_allocation(expr_mpos, 128)
                /// @src 12:2932:3001  "assembly (\"memory-safe\") {..."
                var_value := tload(/** @src 12:2878:2921  "keccak256(abi.encode(key1, key2, baseSlot))" */ keccak256(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _1, mload(/** @src 12:2878:2921  "keccak256(abi.encode(key1, key2, baseSlot))" */ expr_mpos)))
            }
            /// @ast-id 5612 @src 10:273:764  "function safeTransfer(address token, address to, uint256 value) internal {..."
            function fun_safeTransfer(var_token, var_to, var_value)
            {
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                if /** @src 10:364:385  "token.code.length > 0" */ iszero(/** @src 10:364:381  "token.code.length" */ extcodesize(var_token))
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                {
                    mstore(/** @src 10:384:385  "0" */ 0x00, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(226, 0x3c11a9c5))
                    revert(/** @src 10:384:385  "0" */ 0x00, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 4)
                }
                /// @src 10:460:504  "abi.encodeCall(IERC20.transfer, (to, value))"
                let expr_5586_mpos := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                /// @src 10:460:504  "abi.encodeCall(IERC20.transfer, (to, value))"
                let _1 := add(expr_5586_mpos, 0x20)
                mstore(_1, shl(224, 0xa9059cbb))
                let _2 := sub(abi_encode_address_uint256(add(expr_5586_mpos, 36), var_to, var_value), expr_5586_mpos)
                mstore(expr_5586_mpos, add(_2, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(31)))
                /// @src 10:460:504  "abi.encodeCall(IERC20.transfer, (to, value))"
                finalize_allocation(expr_5586_mpos, _2)
                /// @src 10:449:505  "token.call(abi.encodeCall(IERC20.transfer, (to, value)))"
                let expr_5587_component := call(gas(), var_token, /** @src 10:384:385  "0" */ 0x00, /** @src 10:449:505  "token.call(abi.encodeCall(IERC20.transfer, (to, value)))" */ _1, mload(expr_5586_mpos), /** @src 10:384:385  "0" */ 0x00, 0x00)
                /// @src 10:449:505  "token.call(abi.encodeCall(IERC20.transfer, (to, value)))"
                let expr_5587_component_2_mpos := extract_returndata()
                /// @src 10:515:658  "if (!success) {..."
                if /** @src 10:519:527  "!success" */ iszero(expr_5587_component)
                /// @src 10:515:658  "if (!success) {..."
                {
                    /// @src 10:543:648  "assembly (\"memory-safe\") {..."
                    revert(add(expr_5587_component_2_mpos, /** @src 10:460:504  "abi.encodeCall(IERC20.transfer, (to, value))" */ 0x20), /** @src 10:543:648  "assembly (\"memory-safe\") {..." */ mload(expr_5587_component_2_mpos))
                }
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                let _3 := mload(/** @src 10:675:692  "returndata.length" */ expr_5587_component_2_mpos)
                /// @src 10:675:731  "returndata.length == 0 || abi.decode(returndata, (bool))"
                let expr := /** @src 10:675:697  "returndata.length == 0" */ iszero(_3)
                /// @src 10:675:731  "returndata.length == 0 || abi.decode(returndata, (bool))"
                if iszero(expr)
                {
                    expr := /** @src 10:701:731  "abi.decode(returndata, (bool))" */ abi_decode_bool_fromMemory(add(expr_5587_component_2_mpos, /** @src 10:460:504  "abi.encodeCall(IERC20.transfer, (to, value))" */ 0x20), /** @src 10:701:731  "abi.decode(returndata, (bool))" */ add(add(expr_5587_component_2_mpos, _3), /** @src 10:460:504  "abi.encodeCall(IERC20.transfer, (to, value))" */ 0x20))
                }
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                if iszero(expr)
                {
                    mstore(/** @src 10:384:385  "0" */ 0x00, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(226, 0x0bc11c3f))
                    revert(/** @src 10:384:385  "0" */ 0x00, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 4)
                }
            }
            /// @ast-id 6019 @src 12:855:1102  "function toUint128(uint256 x) internal pure returns (uint128) {..."
            function fun_toUint128(var_x) -> var
            {
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                if /** @src 12:935:957  "x <= type(uint128).max" */ gt(var_x, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)
                {
                    mstore(0, shl(227, 0x1cb1a8e3))
                    revert(0, 4)
                }
                /// @src 12:1078:1095  "return uint128(x)"
                var := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 12:1085:1095  "uint128(x)" */ var_x, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)
            }
            /// @ast-id 5673 @src 10:770:1293  "function safeTransferFrom(address token, address from, address to, uint256 value) internal {..."
            function fun_safeTransferFrom(var_token, var_from, var_to, var_value)
            {
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                if /** @src 10:879:900  "token.code.length > 0" */ iszero(/** @src 10:879:896  "token.code.length" */ extcodesize(var_token))
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                {
                    mstore(/** @src 10:899:900  "0" */ 0x00, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(226, 0x3c11a9c5))
                    revert(/** @src 10:899:900  "0" */ 0x00, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 4)
                }
                /// @src 10:975:1029  "abi.encodeCall(IERC20.transferFrom, (from, to, value))"
                let expr_5647_mpos := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                /// @src 10:975:1029  "abi.encodeCall(IERC20.transferFrom, (from, to, value))"
                let _1 := add(expr_5647_mpos, 0x20)
                mstore(_1, shl(224, 0x23b872dd))
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                mstore(/** @src 10:975:1029  "abi.encodeCall(IERC20.transferFrom, (from, to, value))" */ add(expr_5647_mpos, 36), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(var_from, 0xffffffffffffffffffffffffffffffffffffffff))
                mstore(add(/** @src 10:975:1029  "abi.encodeCall(IERC20.transferFrom, (from, to, value))" */ expr_5647_mpos, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 68), and(var_to, 0xffffffffffffffffffffffffffffffffffffffff))
                mstore(add(/** @src 10:975:1029  "abi.encodeCall(IERC20.transferFrom, (from, to, value))" */ expr_5647_mpos, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 100), var_value)
                /// @src 10:975:1029  "abi.encodeCall(IERC20.transferFrom, (from, to, value))"
                mstore(expr_5647_mpos, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 100)
                /// @src 10:975:1029  "abi.encodeCall(IERC20.transferFrom, (from, to, value))"
                finalize_allocation(expr_5647_mpos, 132)
                /// @src 10:964:1030  "token.call(abi.encodeCall(IERC20.transferFrom, (from, to, value)))"
                let expr_5648_component := call(gas(), var_token, /** @src 10:899:900  "0" */ 0x00, /** @src 10:964:1030  "token.call(abi.encodeCall(IERC20.transferFrom, (from, to, value)))" */ _1, mload(expr_5647_mpos), /** @src 10:899:900  "0" */ 0x00, 0x00)
                /// @src 10:964:1030  "token.call(abi.encodeCall(IERC20.transferFrom, (from, to, value)))"
                let expr_5648_component_2_mpos := extract_returndata()
                /// @src 10:1040:1183  "if (!success) {..."
                if /** @src 10:1044:1052  "!success" */ iszero(expr_5648_component)
                /// @src 10:1040:1183  "if (!success) {..."
                {
                    /// @src 10:1068:1173  "assembly (\"memory-safe\") {..."
                    revert(add(expr_5648_component_2_mpos, /** @src 10:975:1029  "abi.encodeCall(IERC20.transferFrom, (from, to, value))" */ 0x20), /** @src 10:1068:1173  "assembly (\"memory-safe\") {..." */ mload(expr_5648_component_2_mpos))
                }
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                let _2 := mload(/** @src 10:1200:1217  "returndata.length" */ expr_5648_component_2_mpos)
                /// @src 10:1200:1256  "returndata.length == 0 || abi.decode(returndata, (bool))"
                let expr := /** @src 10:1200:1222  "returndata.length == 0" */ iszero(_2)
                /// @src 10:1200:1256  "returndata.length == 0 || abi.decode(returndata, (bool))"
                if iszero(expr)
                {
                    expr := /** @src 10:1226:1256  "abi.decode(returndata, (bool))" */ abi_decode_bool_fromMemory(add(expr_5648_component_2_mpos, /** @src 10:975:1029  "abi.encodeCall(IERC20.transferFrom, (from, to, value))" */ 0x20), /** @src 10:1226:1256  "abi.decode(returndata, (bool))" */ add(add(expr_5648_component_2_mpos, _2), /** @src 10:975:1029  "abi.encodeCall(IERC20.transferFrom, (from, to, value))" */ 0x20))
                }
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                if iszero(expr)
                {
                    mstore(/** @src 10:899:900  "0" */ 0x00, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(226, 0x07b7b467))
                    revert(/** @src 10:899:900  "0" */ 0x00, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 4)
                }
            }
            /// @ast-id 3558 @src 0:47821:48796  "function _updatePosition(Market memory market, bytes32 id, address user)..."
            function fun_updatePosition(var_market_3453_mpos, var_id, var_user) -> var, var_1, var_2
            {
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                mstore(/** @src 0:47998:48006  "position" */ 0x00, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ var_id)
                mstore(0x20, /** @src 0:47998:48006  "position" */ 0x00)
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                let dataSlot := keccak256(/** @src 0:47998:48006  "position" */ 0x00, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x40)
                /// @src 0:47998:48016  "position[id][user]"
                let dataSlot_1 := /** @src -1:-1:-1 */ 0
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:47998:48016  "position[id][user]" */ var_user, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                mstore(0x20, /** @src 0:47998:48010  "position[id]" */ dataSlot)
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                dataSlot_1 := keccak256(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x40)
                /// @src 0:48091:48127  "updatePositionView(market, id, user)"
                let expr_3485_component, expr_3485_component_1, expr_3485_component_2 := fun_updatePositionView(var_market_3453_mpos, var_id, var_user)
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                let _1 := sload(/** @src 0:47998:48016  "position[id][user]" */ dataSlot_1)
                /// @src 0:48163:48191  "_position.credit - newCredit"
                let expr := checked_sub_uint128(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(_1, 0xffffffffffffffffffffffffffffffff), /** @src 0:48163:48191  "_position.credit - newCredit" */ expr_3485_component)
                /// @src 0:48230:48266  "_position.pendingFee - newPendingFee"
                let expr_1 := checked_sub_uint128(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shr(128, _1), /** @src 0:48230:48266  "_position.pendingFee - newPendingFee" */ expr_3485_component_1)
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                sstore(/** @src 0:47998:48016  "position[id][user]" */ dataSlot_1, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ or(and(sload(/** @src 0:47998:48016  "position[id][user]" */ dataSlot_1), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(0xffffffffffffffffffffffffffffffff)), and(/** @src 0:48277:48305  "_position.credit = newCredit" */ expr_3485_component, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)))
                mstore(/** @src 0:47998:48006  "position" */ 0x00, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ var_id)
                mstore(0x20, /** @src 0:48342:48353  "marketState" */ 0x01)
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                let _2 := shr(128, sload(keccak256(/** @src 0:47998:48006  "position" */ 0x00, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x40)))
                /// @src 0:48315:48339  "_position.lastLossFactor"
                let _3 := add(/** @src 0:47998:48016  "position[id][user]" */ dataSlot_1, /** @src 0:48342:48353  "marketState" */ 0x01)
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                sstore(/** @src 0:48315:48368  "_position.lastLossFactor = marketState[id].lossFactor" */ _3, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ or(and(sload(/** @src 0:48315:48368  "_position.lastLossFactor = marketState[id].lossFactor" */ _3), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ not(0xffffffffffffffffffffffffffffffff)), and(/** @src 0:48315:48368  "_position.lastLossFactor = marketState[id].lossFactor" */ _2, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)))
                /// @src 0:48378:48414  "_position.pendingFee = newPendingFee"
                update_storage_value_offset_uint128_to_uint128(/** @src 0:47998:48016  "position[id][user]" */ dataSlot_1, /** @src 0:48378:48414  "_position.pendingFee = newPendingFee" */ expr_3485_component_1)
                /// @src 0:48508:48556  "_position.lastAccrual = uint128(block.timestamp)"
                update_storage_value_offset_uint128_to_uint128(_3, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:48540:48555  "block.timestamp" */ timestamp(), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff))
                let _4 := and(/** @src 0:48605:48635  "UtilsLib.toUint128(accruedFee)" */ expr_3485_component_2, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)
                /// @src 0:48605:48635  "UtilsLib.toUint128(accruedFee)"
                let expr_2 := fun_toUint128(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _4)
                mstore(/** @src 0:47998:48006  "position" */ 0x00, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ var_id)
                mstore(0x20, /** @src 0:48342:48353  "marketState" */ 0x01)
                /// @src 0:48566:48601  "marketState[id].continuousFeeCredit"
                let _5 := add(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ keccak256(/** @src 0:47998:48006  "position" */ 0x00, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x40), /** @src 0:48342:48353  "marketState" */ 0x01)
                /// @src 0:48566:48635  "marketState[id].continuousFeeCredit += UtilsLib.toUint128(accruedFee)"
                update_storage_value_offset_uint128_to_uint128(_5, checked_add_uint128(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shr(128, sload(/** @src 0:48566:48635  "marketState[id].continuousFeeCredit += UtilsLib.toUint128(accruedFee)" */ _5)), expr_2))
                /// @src 0:48651:48733  "EventsLib.UpdatePosition(id, user, creditDecrease, pendingFeeDecrease, accruedFee)"
                let _6 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(0x40)
                mstore(_6, and(expr, 0xffffffffffffffffffffffffffffffff))
                mstore(add(_6, 0x20), and(expr_1, 0xffffffffffffffffffffffffffffffff))
                mstore(add(_6, 0x40), _4)
                /// @src 0:48651:48733  "EventsLib.UpdatePosition(id, user, creditDecrease, pendingFeeDecrease, accruedFee)"
                log3(_6, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 96, /** @src 0:48651:48733  "EventsLib.UpdatePosition(id, user, creditDecrease, pendingFeeDecrease, accruedFee)" */ 0x8fd212bc8fa18d807a9b47aa2de07104bf036cfcef8ea259157085a1b618a77c, var_id, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:48651:48733  "EventsLib.UpdatePosition(id, user, creditDecrease, pendingFeeDecrease, accruedFee)" */ var_user, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                /// @src 0:48744:48789  "return (newCredit, newPendingFee, accruedFee)"
                var := expr_3485_component
                var_1 := expr_3485_component_1
                var_2 := expr_3485_component_2
            }
            /// @ast-id 5183 @src 7:1179:1460  "function maxSettlementFee(uint256 index) pure returns (uint256) {..."
            function fun_maxSettlementFee(var_index) -> var
            {
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                let memPtr := mload(64)
                finalize_allocation_44126(memPtr)
                /// @src 7:314:325  "0.000014e18"
                mstore(memPtr, 0x0cbba106e000)
                mstore(/** @src 7:1256:1450  "[MAX_SETTLEMENT_FEE_0_DAYS, MAX_SETTLEMENT_FEE_1_DAY, MAX_SETTLEMENT_FEE_7_DAYS, MAX_SETTLEMENT_FEE_30_DAYS, MAX_SETTLEMENT_FEE_90_DAYS, MAX_SETTLEMENT_FEE_180_DAYS, MAX_SETTLEMENT_FEE_360_DAYS]" */ add(memPtr, 32), /** @src 7:314:325  "0.000014e18" */ 0x0cbba106e000)
                mstore(/** @src 7:1256:1450  "[MAX_SETTLEMENT_FEE_0_DAYS, MAX_SETTLEMENT_FEE_1_DAY, MAX_SETTLEMENT_FEE_7_DAYS, MAX_SETTLEMENT_FEE_30_DAYS, MAX_SETTLEMENT_FEE_90_DAYS, MAX_SETTLEMENT_FEE_180_DAYS, MAX_SETTLEMENT_FEE_360_DAYS]" */ add(memPtr, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 64), /** @src 7:429:440  "0.000098e18" */ 0x592167302000)
                /// @src 7:314:325  "0.000014e18"
                mstore(/** @src 7:1256:1450  "[MAX_SETTLEMENT_FEE_0_DAYS, MAX_SETTLEMENT_FEE_1_DAY, MAX_SETTLEMENT_FEE_7_DAYS, MAX_SETTLEMENT_FEE_30_DAYS, MAX_SETTLEMENT_FEE_90_DAYS, MAX_SETTLEMENT_FEE_180_DAYS, MAX_SETTLEMENT_FEE_360_DAYS]" */ add(memPtr, 96), /** @src 7:488:499  "0.000417e18" */ 0x017b4260df1000)
                /// @src 7:314:325  "0.000014e18"
                mstore(/** @src 7:1256:1450  "[MAX_SETTLEMENT_FEE_0_DAYS, MAX_SETTLEMENT_FEE_1_DAY, MAX_SETTLEMENT_FEE_7_DAYS, MAX_SETTLEMENT_FEE_30_DAYS, MAX_SETTLEMENT_FEE_90_DAYS, MAX_SETTLEMENT_FEE_180_DAYS, MAX_SETTLEMENT_FEE_360_DAYS]" */ add(memPtr, 128), /** @src 7:547:557  "0.00125e18" */ 0x0470de4df82000)
                /// @src 7:314:325  "0.000014e18"
                mstore(/** @src 7:1256:1450  "[MAX_SETTLEMENT_FEE_0_DAYS, MAX_SETTLEMENT_FEE_1_DAY, MAX_SETTLEMENT_FEE_7_DAYS, MAX_SETTLEMENT_FEE_30_DAYS, MAX_SETTLEMENT_FEE_90_DAYS, MAX_SETTLEMENT_FEE_180_DAYS, MAX_SETTLEMENT_FEE_360_DAYS]" */ add(memPtr, 160), /** @src 7:606:615  "0.0025e18" */ 0x08e1bc9bf04000)
                /// @src 7:314:325  "0.000014e18"
                mstore(/** @src 7:1256:1450  "[MAX_SETTLEMENT_FEE_0_DAYS, MAX_SETTLEMENT_FEE_1_DAY, MAX_SETTLEMENT_FEE_7_DAYS, MAX_SETTLEMENT_FEE_30_DAYS, MAX_SETTLEMENT_FEE_90_DAYS, MAX_SETTLEMENT_FEE_180_DAYS, MAX_SETTLEMENT_FEE_360_DAYS]" */ add(memPtr, 192), /** @src 7:664:672  "0.005e18" */ 0x11c37937e08000)
                /// @src 7:1256:1457  "[MAX_SETTLEMENT_FEE_0_DAYS, MAX_SETTLEMENT_FEE_1_DAY, MAX_SETTLEMENT_FEE_7_DAYS, MAX_SETTLEMENT_FEE_30_DAYS, MAX_SETTLEMENT_FEE_90_DAYS, MAX_SETTLEMENT_FEE_180_DAYS, MAX_SETTLEMENT_FEE_360_DAYS][index]"
                let addr := /** @src -1:-1:-1 */ 0
                /// @src 7:1114:1115  "4"
                if iszero(lt(var_index, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x07))
                /// @src 7:1114:1115  "4"
                {
                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                    mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(224, 0x4e487b71))
                    mstore(4, 0x32)
                    revert(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x24)
                }
                /// @src 7:1114:1115  "4"
                addr := add(memPtr, shl(5, var_index))
                /// @src 7:1249:1457  "return [MAX_SETTLEMENT_FEE_0_DAYS, MAX_SETTLEMENT_FEE_1_DAY, MAX_SETTLEMENT_FEE_7_DAYS, MAX_SETTLEMENT_FEE_30_DAYS, MAX_SETTLEMENT_FEE_90_DAYS, MAX_SETTLEMENT_FEE_180_DAYS, MAX_SETTLEMENT_FEE_360_DAYS][index]"
                var := /** @src 7:234:238  "1e36" */ mload(addr)
            }
            /// @ast-id 5994 @src 12:721:849  "function mulDivUp(uint256 x, uint256 y, uint256 d) internal pure returns (uint256) {..."
            function fun_mulDivUp_44146(var_x, var_y) -> var
            {
                /// @src 12:822:827  "x * y"
                let expr := checked_mul_uint256(var_x, var_y)
                /// @src 12:831:836  "d - 1"
                let diff := /** @src -1:-1:-1 */ 0
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                diff := /** @src -1:-1:-1 */ 0
                /// @src 12:822:837  "x * y + (d - 1)"
                let sum := /** @src -1:-1:-1 */ 0
                /// @src 7:892:894  "16"
                sum := add(expr, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x0de0b6b3a763ffff)
                /// @src 7:892:894  "16"
                if gt(expr, sum)
                {
                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                    mstore(0, shl(224, 0x4e487b71))
                    mstore(4, 0x11)
                    revert(0, 0x24)
                }
                /// @src 12:821:842  "(x * y + (d - 1)) / d"
                let r := /** @src -1:-1:-1 */ 0
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                r := /** @src -1:-1:-1 */ 0
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                r := div(sum, /** @src 7:190:194  "1e18" */ 0x0de0b6b3a7640000)
                /// @src 12:814:842  "return (x * y + (d - 1)) / d"
                var := r
            }
            /// @ast-id 5994 @src 12:721:849  "function mulDivUp(uint256 x, uint256 y, uint256 d) internal pure returns (uint256) {..."
            function fun_mulDivUp(var_x, var_y, var_d) -> var
            {
                /// @src 12:822:827  "x * y"
                let expr := checked_mul_uint256(var_x, var_y)
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                let diff := add(var_d, not(0))
                if gt(diff, var_d)
                {
                    mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(224, 0x4e487b71))
                    mstore(4, 0x11)
                    revert(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x24)
                }
                /// @src 12:814:842  "return (x * y + (d - 1)) / d"
                var := /** @src 12:821:842  "(x * y + (d - 1)) / d" */ checked_div_uint256(/** @src 12:822:837  "x * y + (d - 1)" */ checked_add_uint256(expr, /** @src 12:831:836  "d - 1" */ diff), /** @src 12:821:842  "(x * y + (d - 1)) / d" */ var_d)
            }
            /// @ast-id 3825 @src 0:51422:51549  "function hasCredit(bytes32 id, address user) internal view returns (bool) {..."
            function fun_hasCredit(var_id, var_user) -> var_
            {
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                mstore(/** @src 0:51513:51521  "position" */ 0x00, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ var_id)
                mstore(0x20, /** @src 0:51513:51521  "position" */ 0x00)
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                let dataSlot := keccak256(/** @src 0:51513:51521  "position" */ 0x00, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x40)
                /// @src 0:51513:51531  "position[id][user]"
                let dataSlot_1 := /** @src -1:-1:-1 */ 0
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(/** @src 0:51513:51531  "position[id][user]" */ var_user, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                mstore(0x20, /** @src 0:51513:51525  "position[id]" */ dataSlot)
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                dataSlot_1 := keccak256(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x40)
                /// @src 0:51506:51542  "return position[id][user].credit > 0"
                var_ := /** @src 0:51513:51542  "position[id][user].credit > 0" */ iszero(iszero(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ and(sload(/** @src 0:51513:51531  "position[id][user]" */ dataSlot_1), /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0xffffffffffffffffffffffffffffffff)))
            }
            /// @ast-id 6157 @src 12:2350:2657  "function tExchange(uint256 baseSlot, bytes32 key1, address key2, bool value) internal returns (bool previous) {..."
            function fun_tExchange(var_key1, var_key2) -> var_previous
            {
                /// @src 12:2503:2535  "abi.encode(key1, key2, baseSlot)"
                let expr_mpos := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ mload(64)
                /// @src 12:2503:2535  "abi.encode(key1, key2, baseSlot)"
                let _1 := add(expr_mpos, 0x20)
                let tail := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                tail := add(/** @src 12:2503:2535  "abi.encode(key1, key2, baseSlot)" */ expr_mpos, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 128)
                mstore(_1, var_key1)
                mstore(add(/** @src 12:2503:2535  "abi.encode(key1, key2, baseSlot)" */ expr_mpos, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 64), and(var_key2, 0xffffffffffffffffffffffffffffffffffffffff))
                mstore(add(/** @src 12:2503:2535  "abi.encode(key1, key2, baseSlot)" */ expr_mpos, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 96), /** @src 7:945:991  "keccak256(\"morpho.midnight.liquidationLocked\")" */ 0x90e10dad8320b2f9ee6b84bebe89829c27a3fc1209e68031bc1d4b65c22e4da4)
                /// @src 12:2503:2535  "abi.encode(key1, key2, baseSlot)"
                mstore(expr_mpos, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 96)
                /// @src 12:2503:2535  "abi.encode(key1, key2, baseSlot)"
                finalize_allocation(expr_mpos, 128)
                /// @src 12:2493:2536  "keccak256(abi.encode(key1, key2, baseSlot))"
                let _2 := keccak256(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _1, mload(/** @src 12:2493:2536  "keccak256(abi.encode(key1, key2, baseSlot))" */ expr_mpos))
                /// @src 12:2547:2651  "assembly (\"memory-safe\") {..."
                var_previous := tload(_2)
                tstore(_2, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0)
            }
            /// @ast-id 5210 @src 7:1533:1721  "function maxLif(uint256 lltv, uint256 liquidationCursor) pure returns (uint256) {..."
            function fun_maxLif(var_lltv, var_liquidationCursor) -> var
            {
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                let diff := sub(/** @src 7:190:194  "1e18" */ 0x0de0b6b3a7640000, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ var_lltv)
                if gt(diff, /** @src 7:190:194  "1e18" */ 0x0de0b6b3a7640000)
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                {
                    mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(224, 0x4e487b71))
                    mstore(4, 0x11)
                    revert(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x24)
                }
                /// @src 12:653:658  "x * y"
                let _1 := checked_mul_uint256(var_liquidationCursor, diff)
                /// @src 12:652:663  "(x * y) / d"
                let r := /** @src -1:-1:-1 */ 0
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                let _2 := /** @src -1:-1:-1 */ 0
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                _2 := /** @src -1:-1:-1 */ 0
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                r := div(_1, /** @src 7:190:194  "1e18" */ 0x0de0b6b3a7640000)
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                let diff_1 := sub(/** @src 7:190:194  "1e18" */ 0x0de0b6b3a7640000, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ r)
                if gt(diff_1, /** @src 7:190:194  "1e18" */ 0x0de0b6b3a7640000)
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                {
                    mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(224, 0x4e487b71))
                    mstore(4, 0x11)
                    revert(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x24)
                }
                /// @src 12:653:658  "x * y"
                let product := /** @src -1:-1:-1 */ 0
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                product := 0xc097ce7bc90715b34b9f1000000000
                let _3 := /** @src -1:-1:-1 */ 0
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                _3 := /** @src -1:-1:-1 */ 0
                /// @src 12:652:663  "(x * y) / d"
                let r_1 := /** @src -1:-1:-1 */ 0
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                if iszero(/** @src 12:652:663  "(x * y) / d" */ diff_1)
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                {
                    mstore(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ shl(224, 0x4e487b71))
                    mstore(4, 0x12)
                    revert(/** @src -1:-1:-1 */ 0, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0x24)
                }
                r_1 := div(product, /** @src 12:652:663  "(x * y) / d" */ diff_1)
                /// @src 7:1619:1718  "return UtilsLib.mulDivDown(WAD, WAD, WAD - UtilsLib.mulDivDown(liquidationCursor, WAD - lltv, WAD))"
                var := /** @src 12:645:663  "return (x * y) / d" */ r_1
            }
            /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
            function copy_literal_to_memory_a55ffd6cc2b0b507f8827f3c680fa2adb9285b64bf7fb098798ce57c2156693f() -> memPtr
            {
                let size := /** @src -1:-1:-1 */ 0
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                let _1 := /** @src -1:-1:-1 */ 0
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                _1 := /** @src -1:-1:-1 */ 0
                /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                size := 64
                let memPtr_1 := mload(64)
                finalize_allocation(memPtr_1, 64)
                mstore(memPtr_1, 11)
                memPtr := memPtr_1
                mstore(add(memPtr_1, 32), shl(168, 0x600b380380600b5f395ff3))
            }
            /// @ast-id 5805 @src 11:776:1940  "function wExp(int256 x) internal pure returns (uint256) {..."
            function fun_wExp(var_x) -> var
            {
                /// @src 11:823:830  "uint256"
                var := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                /// @src 11:866:1924  "if (x < 0) {..."
                switch /** @src 11:870:875  "x < 0" */ slt(var_x, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0)
                case /** @src 11:866:1924  "if (x < 0) {..." */ 0 {
                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                    let r := sdiv(add(/** @src 11:1219:1229  "x + offset" */ var_x, /** @src 11:1167:1189  "0.32261121498945987e18" */ 0x047a2530d601019e), /** @src 11:969:992  "0.693147180559945309e18" */ 0x099e8db03256ce5d)
                    /// @src 11:1343:1354  "x - q * ln2"
                    let expr := /** @src 11:134:157  "0.004987541511039073e18" */ sub(/** @src 11:1343:1354  "x - q * ln2" */ var_x, /** @src 11:134:157  "0.004987541511039073e18" */ mul(/** @src 11:1347:1354  "q * ln2" */ r, /** @src 11:969:992  "0.693147180559945309e18" */ 0x099e8db03256ce5d))
                    /// @src 0:13935:54527  "contract Midnight is IMidnight {..."
                    let r_1 := sdiv(/** @src 11:134:157  "0.004987541511039073e18" */ mul(/** @src 11:1392:1397  "r * r" */ expr, expr), /** @src 11:1401:1409  "2 * 1e18" */ 0x1bc16d674ec80000)
                    /// @src 11:1525:1552  "secondTerm * r / (3 * 1e18)"
                    let r_2 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                    let _1 := 0
                    _1 := 0
                    r_2 := sdiv(/** @src 11:134:157  "0.004987541511039073e18" */ mul(/** @src 11:1525:1539  "secondTerm * r" */ r_1, expr), /** @src 11:1543:1551  "3 * 1e18" */ 0x29a2241af62c0000)
                    /// @src 11:1875:1909  "return uint256(expR) << uint256(q)"
                    var := /** @src 7:892:894  "16" */ shl(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ r, add(add(add(/** @src 11:1584:1592  "1e18 + r" */ expr, /** @src 11:1584:1605  "1e18 + r + secondTerm" */ r_1), /** @src 11:1584:1617  "1e18 + r + secondTerm + thirdTerm" */ r_2), /** @src 11:1584:1588  "1e18" */ 0x0de0b6b3a7640000))
                    /// @src 11:1875:1909  "return uint256(expR) << uint256(q)"
                    leave
                }
                default /// @src 11:866:1924  "if (x < 0) {..."
                {
                    /// @src 11:909:917  "wExp(-x)"
                    let _2 := fun_wExp(/** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ sub(0, /** @src 11:914:916  "-x" */ var_x))
                    /// @src 11:902:917  "1e36 / wExp(-x)"
                    let r_3 := /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ 0
                    if iszero(_2)
                    {
                        mstore(0, shl(224, 0x4e487b71))
                        mstore(4, 0x12)
                        revert(0, 0x24)
                    }
                    r_3 := div(/** @src 11:902:906  "1e36" */ 0xc097ce7bc90715b34b9f1000000000, /** @src 0:13935:54527  "contract Midnight is IMidnight {..." */ _2)
                    /// @src 11:895:917  "return 1e36 / wExp(-x)"
                    var := r_3
                    leave
                }
            }
        }
        data ".metadata" hex"a164736f6c6343000822000a"
    }
}
