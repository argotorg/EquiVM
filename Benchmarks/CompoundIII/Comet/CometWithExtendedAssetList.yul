/// @use-src 0:"CometConfiguration.sol", 1:"CometCore.sol", 2:"CometMainInterface.sol", 3:"CometMath.sol", 4:"CometStorage.sol", 5:"CometWithExtendedAssetList.sol"
object "CometWithExtendedAssetList_4926" {
    code {
        {
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            let _1 := memoryguard(0x03a0)
            mstore(64, _1)
            if callvalue() { revert(0, 0) }
            let programSize := datasize("CometWithExtendedAssetList_4926")
            let argSize := sub(codesize(), programSize)
            finalize_allocation(_1, argSize)
            codecopy(_1, programSize, argSize)
            if slt(sub(add(_1, argSize), _1), 32)
            {
                revert(/** @src -1:-1:-1 */ 0, 0)
            }
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            let offset := mload(_1)
            if gt(offset, sub(shl(64, 1), 1))
            {
                revert(/** @src -1:-1:-1 */ 0, 0)
            }
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            if slt(sub(add(_1, argSize), add(_1, offset)), 0x02a0)
            {
                revert(/** @src -1:-1:-1 */ 0, 0)
            }
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            let memPtr := mload(64)
            finalize_allocation(memPtr, 0x02a0)
            mstore(memPtr, abi_decode_address_fromMemory(add(_1, offset)))
            let _2 := abi_decode_address_fromMemory(add(add(_1, offset), 32))
            mstore(add(memPtr, 32), _2)
            let _3 := abi_decode_address_fromMemory(add(add(_1, offset), 64))
            mstore(add(memPtr, 64), _3)
            let _4 := abi_decode_address_fromMemory(add(add(_1, offset), 96))
            mstore(add(memPtr, 96), _4)
            let _5 := abi_decode_address_fromMemory(add(add(_1, offset), 128))
            mstore(add(memPtr, 128), _5)
            let _6 := abi_decode_uint64_fromMemory(add(add(_1, offset), 160))
            mstore(add(memPtr, 160), _6)
            let _7 := abi_decode_uint64_fromMemory(add(add(_1, offset), 192))
            mstore(add(memPtr, 192), _7)
            let _8 := abi_decode_uint64_fromMemory(add(add(_1, offset), 224))
            mstore(add(memPtr, 224), _8)
            let _9 := abi_decode_uint64_fromMemory(add(add(_1, offset), 256))
            mstore(add(memPtr, 256), _9)
            let _10 := abi_decode_uint64_fromMemory(add(add(_1, offset), 288))
            mstore(add(memPtr, 288), _10)
            let _11 := abi_decode_uint64_fromMemory(add(add(_1, offset), 320))
            mstore(add(memPtr, 320), _11)
            let _12 := abi_decode_uint64_fromMemory(add(add(_1, offset), 352))
            mstore(add(memPtr, 352), _12)
            let _13 := abi_decode_uint64_fromMemory(add(add(_1, offset), 384))
            mstore(add(memPtr, 384), _13)
            let _14 := abi_decode_uint64_fromMemory(add(add(_1, offset), 416))
            mstore(add(memPtr, 416), _14)
            let _15 := abi_decode_uint64_fromMemory(add(add(_1, offset), 448))
            mstore(add(memPtr, 448), _15)
            let _16 := abi_decode_uint64_fromMemory(add(add(_1, offset), 480))
            mstore(add(memPtr, 480), _16)
            let _17 := abi_decode_uint64_fromMemory(add(add(_1, offset), 512))
            mstore(add(memPtr, 512), _17)
            let _18 := abi_decode_uint104_fromMemory(add(add(_1, offset), 544))
            mstore(add(memPtr, 544), _18)
            let _19 := abi_decode_uint104_fromMemory(add(add(_1, offset), 576))
            mstore(add(memPtr, 576), _19)
            let _20 := abi_decode_uint104_fromMemory(add(add(_1, offset), 608))
            mstore(add(memPtr, 608), _20)
            let offset_1 := mload(add(add(_1, offset), 640))
            if gt(offset_1, sub(shl(64, 1), 1))
            {
                revert(/** @src -1:-1:-1 */ 0, 0)
            }
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            if iszero(slt(add(add(add(_1, offset), offset_1), 0x1f), add(_1, argSize)))
            {
                revert(/** @src -1:-1:-1 */ 0, 0)
            }
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            let _21 := mload(add(add(_1, offset), offset_1))
            if gt(_21, sub(shl(64, 1), 1))
            {
                mstore(/** @src -1:-1:-1 */ 0, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ shl(224, 0x4e487b71))
                mstore(4, 0x41)
                revert(/** @src -1:-1:-1 */ 0, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0x24)
            }
            let memPtr_1 := mload(64)
            finalize_allocation(memPtr_1, add(shl(5, _21), 32))
            let dst := memPtr_1
            mstore(memPtr_1, _21)
            dst := add(memPtr_1, 32)
            if gt(add(add(add(add(_1, offset), offset_1), mul(_21, 224)), 32), add(_1, argSize))
            {
                revert(/** @src -1:-1:-1 */ 0, 0)
            }
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            let src := add(add(add(_1, offset), offset_1), 32)
            for { }
            lt(src, add(add(add(add(_1, offset), offset_1), mul(_21, 224)), 32))
            { src := add(src, 224) }
            {
                if slt(sub(add(_1, argSize), src), 224)
                {
                    /// @src -1:-1:-1
                    let _22 := 0
                    /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                    revert(/** @src -1:-1:-1 */ _22, _22)
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let memPtr_2 := mload(64)
                finalize_allocation(memPtr_2, 224)
                mstore(memPtr_2, abi_decode_address_fromMemory(src))
                mstore(add(memPtr_2, 32), abi_decode_address_fromMemory(add(src, 32)))
                mstore(add(memPtr_2, 64), abi_decode_uint8_fromMemory(add(src, 64)))
                mstore(add(memPtr_2, 96), abi_decode_uint64_fromMemory(add(src, 96)))
                mstore(add(memPtr_2, 128), abi_decode_uint64_fromMemory(add(src, 128)))
                mstore(add(memPtr_2, 160), abi_decode_uint64_fromMemory(add(src, 160)))
                let value := mload(add(src, 192))
                if iszero(eq(value, and(value, sub(shl(128, 1), 1))))
                {
                    /// @src -1:-1:-1
                    let _23 := 0
                    /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                    revert(/** @src -1:-1:-1 */ _23, _23)
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                mstore(add(memPtr_2, 192), value)
                mstore(dst, memPtr_2)
                dst := add(dst, 32)
            }
            mstore(add(memPtr, 640), memPtr_1)
            let cleaned := and(mload(add(memPtr, 64)), sub(shl(160, 1), 1))
            /// @src 5:4657:4703  "IERC20NonStandard(config.baseToken).decimals()"
            let _24 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
            /// @src 5:4657:4703  "IERC20NonStandard(config.baseToken).decimals()"
            mstore(_24, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ shl(224, 0x313ce567))
            /// @src 5:4657:4703  "IERC20NonStandard(config.baseToken).decimals()"
            let _25 := staticcall(gas(), cleaned, _24, 4, _24, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 32)
            /// @src 5:4657:4703  "IERC20NonStandard(config.baseToken).decimals()"
            if iszero(_25)
            {
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let pos := mload(64)
                returndatacopy(pos, /** @src -1:-1:-1 */ 0, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ returndatasize())
                revert(pos, returndatasize())
            }
            /// @src 5:4657:4703  "IERC20NonStandard(config.baseToken).decimals()"
            let expr := /** @src -1:-1:-1 */ 0
            /// @src 5:4657:4703  "IERC20NonStandard(config.baseToken).decimals()"
            if _25
            {
                let _26 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 32
                /// @src 5:4657:4703  "IERC20NonStandard(config.baseToken).decimals()"
                if gt(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 32, /** @src 5:4657:4703  "IERC20NonStandard(config.baseToken).decimals()" */ returndatasize()) { _26 := returndatasize() }
                finalize_allocation(_24, _26)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                if slt(sub(/** @src 5:4657:4703  "IERC20NonStandard(config.baseToken).decimals()" */ add(_24, _26), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _24), 32)
                {
                    revert(/** @src -1:-1:-1 */ expr, expr)
                }
                /// @src 5:4657:4703  "IERC20NonStandard(config.baseToken).decimals()"
                expr := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ abi_decode_uint8_fromMemory(_24)
            }
            /// @src 5:4713:4768  "if (decimals_ > MAX_BASE_DECIMALS) revert BadDecimals()"
            if /** @src 5:4717:4746  "decimals_ > MAX_BASE_DECIMALS" */ gt(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:4717:4746  "decimals_ > MAX_BASE_DECIMALS" */ expr, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0xff), /** @src 1:999:1001  "18" */ 0x12)
            /// @src 5:4713:4768  "if (decimals_ > MAX_BASE_DECIMALS) revert BadDecimals()"
            {
                /// @src 5:4755:4768  "BadDecimals()"
                let _27 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                /// @src 5:4755:4768  "BadDecimals()"
                mstore(_27, shl(229, 0x0456c659))
                revert(_27, /** @src 5:4657:4703  "IERC20NonStandard(config.baseToken).decimals()" */ 4)
            }
            /// @src 5:4778:4847  "if (config.storeFrontPriceFactor > FACTOR_SCALE) revert BadDiscount()"
            if /** @src 5:4782:4825  "config.storeFrontPriceFactor > FACTOR_SCALE" */ gt(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 1:999:1001  "18" */ mload(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ add(memPtr, 416)), sub(shl(64, 1), 1)), /** @src 1:2135:2139  "1e18" */ 0x0de0b6b3a7640000)
            /// @src 5:4778:4847  "if (config.storeFrontPriceFactor > FACTOR_SCALE) revert BadDiscount()"
            {
                /// @src 5:4834:4847  "BadDiscount()"
                let _28 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                /// @src 5:4834:4847  "BadDiscount()"
                mstore(_28, shl(225, 0x24dc918f))
                revert(_28, /** @src 5:4657:4703  "IERC20NonStandard(config.baseToken).decimals()" */ 4)
            }
            /// @src 5:4857:4939  "if (config.assetConfigs.length > MAX_ASSETS_FOR_ASSET_LIST) revert TooManyAssets()"
            if /** @src 5:4861:4915  "config.assetConfigs.length > MAX_ASSETS_FOR_ASSET_LIST" */ gt(/** @src 1:2135:2139  "1e18" */ mload(/** @src 5:4861:4880  "config.assetConfigs" */ mload(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ add(memPtr, 640))), /** @src 5:4424:4426  "24" */ 0x18)
            /// @src 5:4857:4939  "if (config.assetConfigs.length > MAX_ASSETS_FOR_ASSET_LIST) revert TooManyAssets()"
            {
                /// @src 5:4924:4939  "TooManyAssets()"
                let _29 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                /// @src 5:4924:4939  "TooManyAssets()"
                mstore(_29, shl(224, 0xdf8153c7))
                revert(_29, /** @src 5:4657:4703  "IERC20NonStandard(config.baseToken).decimals()" */ 4)
            }
            /// @src 5:4949:5003  "if (config.baseMinForRewards == 0) revert BadMinimum()"
            if /** @src 5:4953:4982  "config.baseMinForRewards == 0" */ iszero(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:4424:4426  "24" */ mload(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ add(memPtr, 544)), sub(shl(104, 1), 1)))
            /// @src 5:4949:5003  "if (config.baseMinForRewards == 0) revert BadMinimum()"
            {
                /// @src 5:4991:5003  "BadMinimum()"
                let _30 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                /// @src 5:4991:5003  "BadMinimum()"
                mstore(_30, shl(224, 0x6e772475))
                revert(_30, /** @src 5:4657:4703  "IERC20NonStandard(config.baseToken).decimals()" */ 4)
            }
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            let cleaned_1 := and(mload(add(memPtr, 96)), sub(shl(160, 1), 1))
            /// @src 5:5017:5065  "IPriceFeed(config.baseTokenPriceFeed).decimals()"
            let _31 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
            /// @src 5:5017:5065  "IPriceFeed(config.baseTokenPriceFeed).decimals()"
            mstore(_31, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ shl(224, 0x313ce567))
            /// @src 5:5017:5065  "IPriceFeed(config.baseTokenPriceFeed).decimals()"
            let _32 := staticcall(gas(), cleaned_1, _31, /** @src 5:4657:4703  "IERC20NonStandard(config.baseToken).decimals()" */ 4, /** @src 5:5017:5065  "IPriceFeed(config.baseTokenPriceFeed).decimals()" */ _31, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 32)
            /// @src 5:5017:5065  "IPriceFeed(config.baseTokenPriceFeed).decimals()"
            if iszero(_32)
            {
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let pos_1 := mload(64)
                returndatacopy(pos_1, /** @src -1:-1:-1 */ 0, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ returndatasize())
                revert(pos_1, returndatasize())
            }
            /// @src 5:5017:5065  "IPriceFeed(config.baseTokenPriceFeed).decimals()"
            let expr_1 := /** @src -1:-1:-1 */ 0
            /// @src 5:5017:5065  "IPriceFeed(config.baseTokenPriceFeed).decimals()"
            if _32
            {
                let _33 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 32
                /// @src 5:5017:5065  "IPriceFeed(config.baseTokenPriceFeed).decimals()"
                if gt(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 32, /** @src 5:5017:5065  "IPriceFeed(config.baseTokenPriceFeed).decimals()" */ returndatasize()) { _33 := returndatasize() }
                finalize_allocation(_31, _33)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                if slt(sub(/** @src 5:5017:5065  "IPriceFeed(config.baseTokenPriceFeed).decimals()" */ add(_31, _33), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _31), 32)
                {
                    revert(/** @src -1:-1:-1 */ expr_1, expr_1)
                }
                /// @src 5:5017:5065  "IPriceFeed(config.baseTokenPriceFeed).decimals()"
                expr_1 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ abi_decode_uint8_fromMemory(_31)
            }
            /// @src 5:5013:5110  "if (IPriceFeed(config.baseTokenPriceFeed).decimals() != PRICE_FEED_DECIMALS) revert BadDecimals()"
            if /** @src 5:5017:5088  "IPriceFeed(config.baseTokenPriceFeed).decimals() != PRICE_FEED_DECIMALS" */ iszero(eq(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:5017:5088  "IPriceFeed(config.baseTokenPriceFeed).decimals() != PRICE_FEED_DECIMALS" */ expr_1, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0xff), /** @src 1:1566:1567  "8" */ 0x08))
            /// @src 5:5013:5110  "if (IPriceFeed(config.baseTokenPriceFeed).decimals() != PRICE_FEED_DECIMALS) revert BadDecimals()"
            {
                /// @src 5:5097:5110  "BadDecimals()"
                let _34 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                /// @src 5:5097:5110  "BadDecimals()"
                mstore(_34, /** @src 5:4755:4768  "BadDecimals()" */ shl(229, 0x0456c659))
                /// @src 5:5097:5110  "BadDecimals()"
                revert(_34, /** @src 5:4657:4703  "IERC20NonStandard(config.baseToken).decimals()" */ 4)
            }
            /// @src 5:5175:5201  "governor = config.governor"
            mstore(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 128, and(mload(/** @src 5:5186:5201  "config.governor" */ memPtr), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(shl(160, 1), 1)))
            /// @src 5:5215:5251  "pauseGuardian = config.pauseGuardian"
            mstore(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 160, and(mload(add(memPtr, 32)), sub(shl(160, 1), 1)))
            /// @src 5:5265:5293  "baseToken = config.baseToken"
            mstore(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 192, and(mload(add(memPtr, 64)), sub(shl(160, 1), 1)))
            /// @src 5:5307:5353  "baseTokenPriceFeed = config.baseTokenPriceFeed"
            mstore(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 224, and(mload(add(memPtr, 96)), sub(shl(160, 1), 1)))
            /// @src 5:5367:5411  "extensionDelegate = config.extensionDelegate"
            mstore(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 256, and(mload(add(memPtr, 128)), sub(shl(160, 1), 1)))
            /// @src 5:5425:5477  "storeFrontPriceFactor = config.storeFrontPriceFactor"
            mstore(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 544, and(/** @src 1:999:1001  "18" */ mload(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ add(memPtr, 416)), sub(shl(64, 1), 1)))
            /// @src 5:5492:5512  "decimals = decimals_"
            mstore(800, expr)
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            let cleaned_2 := and(/** @src 1:1566:1567  "8" */ exp(/** @src 5:5545:5547  "10" */ 0x0a, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:4717:4746  "decimals_ > MAX_BASE_DECIMALS" */ expr, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0xff)), sub(shl(64, 1), 1))
            /// @src 5:5526:5561  "baseScale = uint64(10 ** decimals_)"
            mstore(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 576, /** @src 5:5526:5561  "baseScale = uint64(10 ** decimals_)" */ cleaned_2)
            /// @src 5:5575:5621  "trackingIndexScale = config.trackingIndexScale"
            mstore(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 608, and(/** @src 1:999:1001  "18" */ mload(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ add(memPtr, 448)), sub(shl(64, 1), 1)))
            /// @src 5:5635:5691  "if (baseScale < BASE_ACCRUAL_SCALE) revert BadDecimals()"
            if /** @src 5:5639:5669  "baseScale < BASE_ACCRUAL_SCALE" */ lt(cleaned_2, /** @src 1:1789:1792  "1e6" */ 0x0f4240)
            /// @src 5:5635:5691  "if (baseScale < BASE_ACCRUAL_SCALE) revert BadDecimals()"
            {
                /// @src 5:5678:5691  "BadDecimals()"
                let _35 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                /// @src 5:5678:5691  "BadDecimals()"
                mstore(_35, /** @src 5:4755:4768  "BadDecimals()" */ shl(229, 0x0456c659))
                /// @src 5:5678:5691  "BadDecimals()"
                revert(_35, /** @src 5:4657:4703  "IERC20NonStandard(config.baseToken).decimals()" */ 4)
            }
            /// @src 1:1789:1792  "1e6"
            let _36 := div(/** @src 1:1566:1567  "8" */ mload(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 576), /** @src 1:1789:1792  "1e6" */ 0x0f4240)
            /// @src 5:5705:5758  "accrualDescaleFactor = baseScale / BASE_ACCRUAL_SCALE"
            mstore(864, /** @src 1:1789:1792  "1e6" */ _36)
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            let _37 := and(/** @src 5:4424:4426  "24" */ mload(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ add(memPtr, 544)), sub(shl(104, 1), 1))
            /// @src 5:5773:5817  "baseMinForRewards = config.baseMinForRewards"
            mstore(704, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _37)
            /// @src 5:5831:5887  "baseTrackingSupplySpeed = config.baseTrackingSupplySpeed"
            mstore(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 640, and(/** @src 1:999:1001  "18" */ mload(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ add(memPtr, 480)), sub(shl(64, 1), 1)))
            /// @src 5:5901:5957  "baseTrackingBorrowSpeed = config.baseTrackingBorrowSpeed"
            mstore(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0x02a0, and(/** @src 1:999:1001  "18" */ mload(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ add(memPtr, 512)), sub(shl(64, 1), 1)))
            let _38 := and(/** @src 5:4424:4426  "24" */ mload(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ add(memPtr, 576)), sub(shl(104, 1), 1))
            /// @src 5:5972:6008  "baseBorrowMin = config.baseBorrowMin"
            mstore(736, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _38)
            let _39 := and(/** @src 5:4424:4426  "24" */ mload(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ add(memPtr, 608)), sub(shl(104, 1), 1))
            /// @src 5:6022:6060  "targetReserves = config.targetReserves"
            mstore(768, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _39)
            /// @src 5:6148:6178  "supplyKink = config.supplyKink"
            mstore(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 288, and(/** @src 1:999:1001  "18" */ mload(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ add(memPtr, 160)), sub(shl(64, 1), 1)))
            /// @src 5:6192:6289  "supplyPerSecondInterestRateSlopeLow = config.supplyPerYearInterestRateSlopeLow / SECONDS_PER_YEAR"
            mstore(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 320, and(/** @src 1:1677:1687  "31_536_000" */ div(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 1:999:1001  "18" */ mload(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ add(memPtr, 192)), sub(shl(64, 1), 1)), /** @src 1:1677:1687  "31_536_000" */ 0x01e13380), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(shl(64, 1), 1)))
            /// @src 5:6303:6402  "supplyPerSecondInterestRateSlopeHigh = config.supplyPerYearInterestRateSlopeHigh / SECONDS_PER_YEAR"
            mstore(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 352, and(/** @src 1:1677:1687  "31_536_000" */ div(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 1:999:1001  "18" */ mload(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ add(memPtr, 224)), sub(shl(64, 1), 1)), /** @src 1:1677:1687  "31_536_000" */ 0x01e13380), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(shl(64, 1), 1)))
            /// @src 5:6416:6505  "supplyPerSecondInterestRateBase = config.supplyPerYearInterestRateBase / SECONDS_PER_YEAR"
            mstore(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 384, and(/** @src 1:1677:1687  "31_536_000" */ div(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 1:999:1001  "18" */ mload(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ add(memPtr, 256)), sub(shl(64, 1), 1)), /** @src 1:1677:1687  "31_536_000" */ 0x01e13380), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(shl(64, 1), 1)))
            /// @src 5:6519:6549  "borrowKink = config.borrowKink"
            mstore(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 416, and(/** @src 1:999:1001  "18" */ mload(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ add(memPtr, 288)), sub(shl(64, 1), 1)))
            /// @src 5:6563:6660  "borrowPerSecondInterestRateSlopeLow = config.borrowPerYearInterestRateSlopeLow / SECONDS_PER_YEAR"
            mstore(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 448, and(/** @src 1:1677:1687  "31_536_000" */ div(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 1:999:1001  "18" */ mload(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ add(memPtr, 320)), sub(shl(64, 1), 1)), /** @src 1:1677:1687  "31_536_000" */ 0x01e13380), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(shl(64, 1), 1)))
            /// @src 5:6674:6773  "borrowPerSecondInterestRateSlopeHigh = config.borrowPerYearInterestRateSlopeHigh / SECONDS_PER_YEAR"
            mstore(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 480, and(/** @src 1:1677:1687  "31_536_000" */ div(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 1:999:1001  "18" */ mload(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ add(memPtr, 352)), sub(shl(64, 1), 1)), /** @src 1:1677:1687  "31_536_000" */ 0x01e13380), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(shl(64, 1), 1)))
            /// @src 5:6787:6876  "borrowPerSecondInterestRateBase = config.borrowPerYearInterestRateBase / SECONDS_PER_YEAR"
            mstore(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 512, and(/** @src 1:1677:1687  "31_536_000" */ div(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 1:999:1001  "18" */ mload(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ add(memPtr, 384)), sub(shl(64, 1), 1)), /** @src 1:1677:1687  "31_536_000" */ 0x01e13380), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(shl(64, 1), 1)))
            let _40 := and(/** @src 1:2135:2139  "1e18" */ mload(/** @src 5:6941:6960  "config.assetConfigs" */ mload(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ add(memPtr, 640))), 0xff)
            /// @src 5:6923:6968  "numAssets = uint8(config.assetConfigs.length)"
            mstore(832, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _40)
            let cleaned_3 := and(mload(256), sub(shl(160, 1), 1))
            /// @src 5:7009:7070  "IAssetListFactoryHolder(extensionDelegate).assetListFactory()"
            let _41 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
            /// @src 5:7009:7070  "IAssetListFactoryHolder(extensionDelegate).assetListFactory()"
            mstore(_41, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ shl(227, 0x0e085c5b))
            /// @src 5:7009:7070  "IAssetListFactoryHolder(extensionDelegate).assetListFactory()"
            let _42 := staticcall(gas(), cleaned_3, _41, /** @src 5:4657:4703  "IERC20NonStandard(config.baseToken).decimals()" */ 4, /** @src 5:7009:7070  "IAssetListFactoryHolder(extensionDelegate).assetListFactory()" */ _41, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 32)
            /// @src 5:7009:7070  "IAssetListFactoryHolder(extensionDelegate).assetListFactory()"
            if iszero(_42)
            {
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let pos_2 := mload(64)
                returndatacopy(pos_2, /** @src -1:-1:-1 */ 0, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ returndatasize())
                revert(pos_2, returndatasize())
            }
            /// @src 5:7009:7070  "IAssetListFactoryHolder(extensionDelegate).assetListFactory()"
            let expr_2 := /** @src -1:-1:-1 */ 0
            /// @src 5:7009:7070  "IAssetListFactoryHolder(extensionDelegate).assetListFactory()"
            if _42
            {
                let _43 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 32
                /// @src 5:7009:7070  "IAssetListFactoryHolder(extensionDelegate).assetListFactory()"
                if gt(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 32, /** @src 5:7009:7070  "IAssetListFactoryHolder(extensionDelegate).assetListFactory()" */ returndatasize()) { _43 := returndatasize() }
                finalize_allocation(_41, _43)
                /// @src 1:1677:1687  "31_536_000"
                if slt(sub(/** @src 5:7009:7070  "IAssetListFactoryHolder(extensionDelegate).assetListFactory()" */ add(_41, _43), /** @src 1:1677:1687  "31_536_000" */ _41), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 32)
                /// @src 1:1677:1687  "31_536_000"
                {
                    /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                    revert(/** @src -1:-1:-1 */ expr_2, expr_2)
                }
                /// @src 5:7009:7070  "IAssetListFactoryHolder(extensionDelegate).assetListFactory()"
                expr_2 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ abi_decode_address_fromMemory(/** @src 1:1677:1687  "31_536_000" */ _41)
            }
            /// @src 5:7088:7107  "config.assetConfigs"
            let _mpos := mload(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ add(memPtr, 640))
            /// @src 5:6991:7108  "IAssetListFactory(IAssetListFactoryHolder(extensionDelegate).assetListFactory()).createAssetList(config.assetConfigs)"
            let _44 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
            /// @src 5:6991:7108  "IAssetListFactory(IAssetListFactoryHolder(extensionDelegate).assetListFactory()).createAssetList(config.assetConfigs)"
            mstore(_44, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ shl(224, 0xba15b9d1))
            /// @src 1:1677:1687  "31_536_000"
            let tail := add(/** @src 5:6991:7108  "IAssetListFactory(IAssetListFactoryHolder(extensionDelegate).assetListFactory()).createAssetList(config.assetConfigs)" */ _44, /** @src 1:1677:1687  "31_536_000" */ 36)
            mstore(/** @src 5:6991:7108  "IAssetListFactory(IAssetListFactoryHolder(extensionDelegate).assetListFactory()).createAssetList(config.assetConfigs)" */ add(_44, /** @src 5:4657:4703  "IERC20NonStandard(config.baseToken).decimals()" */ 4), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 32)
            /// @src 1:1677:1687  "31_536_000"
            let pos_3 := tail
            let length := /** @src 1:2135:2139  "1e18" */ mload(/** @src 1:1677:1687  "31_536_000" */ _mpos)
            mstore(tail, length)
            pos_3 := add(/** @src 5:6991:7108  "IAssetListFactory(IAssetListFactoryHolder(extensionDelegate).assetListFactory()).createAssetList(config.assetConfigs)" */ _44, /** @src 1:1677:1687  "31_536_000" */ 68)
            let srcPtr := add(_mpos, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 32)
            /// @src 1:1677:1687  "31_536_000"
            let i := /** @src -1:-1:-1 */ 0
            /// @src 1:1677:1687  "31_536_000"
            for { } lt(i, length) { i := add(i, 1) }
            {
                let _45 := mload(srcPtr)
                mstore(pos_3, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 1:1677:1687  "31_536_000" */ mload(_45), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(shl(160, 1), 1)))
                /// @src 1:1677:1687  "31_536_000"
                mstore(add(pos_3, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 32), and(/** @src 1:1677:1687  "31_536_000" */ mload(add(_45, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 32)), sub(shl(160, 1), 1)))
                /// @src 1:1677:1687  "31_536_000"
                mstore(add(pos_3, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 64), and(/** @src 1:1677:1687  "31_536_000" */ mload(add(_45, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 64)), 0xff))
                /// @src 1:1677:1687  "31_536_000"
                mstore(add(pos_3, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 96), and(/** @src 1:1677:1687  "31_536_000" */ mload(add(_45, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 96)), sub(shl(64, 1), 1)))
                /// @src 1:1677:1687  "31_536_000"
                mstore(add(pos_3, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 128), and(/** @src 1:1677:1687  "31_536_000" */ mload(add(_45, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 128)), sub(shl(64, 1), 1)))
                /// @src 1:1677:1687  "31_536_000"
                mstore(add(pos_3, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 160), and(/** @src 1:1677:1687  "31_536_000" */ mload(add(_45, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 160)), sub(shl(64, 1), 1)))
                /// @src 1:1677:1687  "31_536_000"
                mstore(add(pos_3, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 192), and(/** @src 1:1677:1687  "31_536_000" */ mload(add(_45, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 192)), sub(shl(128, 1), 1)))
                /// @src 1:1677:1687  "31_536_000"
                pos_3 := add(pos_3, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 224)
                /// @src 1:1677:1687  "31_536_000"
                srcPtr := add(srcPtr, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 32)
            }
            /// @src 5:6991:7108  "IAssetListFactory(IAssetListFactoryHolder(extensionDelegate).assetListFactory()).createAssetList(config.assetConfigs)"
            let _46 := call(gas(), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:6991:7071  "IAssetListFactory(IAssetListFactoryHolder(extensionDelegate).assetListFactory())" */ expr_2, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(shl(160, 1), 1)), /** @src -1:-1:-1 */ 0, /** @src 5:6991:7108  "IAssetListFactory(IAssetListFactoryHolder(extensionDelegate).assetListFactory()).createAssetList(config.assetConfigs)" */ _44, sub(pos_3, _44), _44, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 32)
            /// @src 5:6991:7108  "IAssetListFactory(IAssetListFactoryHolder(extensionDelegate).assetListFactory()).createAssetList(config.assetConfigs)"
            if iszero(_46)
            {
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let pos_4 := mload(64)
                returndatacopy(pos_4, /** @src -1:-1:-1 */ 0, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ returndatasize())
                revert(pos_4, returndatasize())
            }
            /// @src 5:6991:7108  "IAssetListFactory(IAssetListFactoryHolder(extensionDelegate).assetListFactory()).createAssetList(config.assetConfigs)"
            let expr_3 := /** @src -1:-1:-1 */ 0
            /// @src 5:6991:7108  "IAssetListFactory(IAssetListFactoryHolder(extensionDelegate).assetListFactory()).createAssetList(config.assetConfigs)"
            if _46
            {
                let _47 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 32
                /// @src 5:6991:7108  "IAssetListFactory(IAssetListFactoryHolder(extensionDelegate).assetListFactory()).createAssetList(config.assetConfigs)"
                if gt(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 32, /** @src 5:6991:7108  "IAssetListFactory(IAssetListFactoryHolder(extensionDelegate).assetListFactory()).createAssetList(config.assetConfigs)" */ returndatasize()) { _47 := returndatasize() }
                finalize_allocation(_44, _47)
                /// @src 1:1677:1687  "31_536_000"
                if slt(sub(/** @src 5:6991:7108  "IAssetListFactory(IAssetListFactoryHolder(extensionDelegate).assetListFactory()).createAssetList(config.assetConfigs)" */ add(_44, _47), /** @src 1:1677:1687  "31_536_000" */ _44), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 32)
                /// @src 1:1677:1687  "31_536_000"
                {
                    /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                    revert(/** @src -1:-1:-1 */ expr_3, expr_3)
                }
                /// @src 5:6991:7108  "IAssetListFactory(IAssetListFactoryHolder(extensionDelegate).assetListFactory()).createAssetList(config.assetConfigs)"
                expr_3 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ abi_decode_address_fromMemory(/** @src 1:1677:1687  "31_536_000" */ _44)
            }
            /// @src 5:6979:7108  "assetList = IAssetListFactory(IAssetListFactoryHolder(extensionDelegate).assetListFactory()).createAssetList(config.assetConfigs)"
            mstore(896, expr_3)
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            let _48 := mload(64)
            codecopy(_48, dataoffset("CometWithExtendedAssetList_4926_deployed"), datasize("CometWithExtendedAssetList_4926_deployed"))
            setimmutable(_48, "1249", mload(128))
            setimmutable(_48, "1253", mload(160))
            setimmutable(_48, "1257", mload(192))
            setimmutable(_48, "1261", mload(224))
            setimmutable(_48, "1265", mload(256))
            setimmutable(_48, "1269", mload(288))
            setimmutable(_48, "1273", mload(320))
            setimmutable(_48, "1277", mload(352))
            setimmutable(_48, "1281", mload(384))
            setimmutable(_48, "1285", mload(416))
            setimmutable(_48, "1289", mload(448))
            setimmutable(_48, "1293", mload(480))
            setimmutable(_48, "1297", mload(512))
            setimmutable(_48, "1301", mload(544))
            setimmutable(_48, "1305", mload(576))
            setimmutable(_48, "1309", mload(608))
            setimmutable(_48, "1313", mload(640))
            setimmutable(_48, "1317", mload(0x02a0))
            setimmutable(_48, "1321", mload(/** @src 5:5773:5817  "baseMinForRewards = config.baseMinForRewards" */ 704))
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            setimmutable(_48, "1325", mload(/** @src 5:5972:6008  "baseBorrowMin = config.baseBorrowMin" */ 736))
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            setimmutable(_48, "1329", mload(/** @src 5:6022:6060  "targetReserves = config.targetReserves" */ 768))
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            setimmutable(_48, "1333", mload(/** @src 5:5492:5512  "decimals = decimals_" */ 800))
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            setimmutable(_48, "1337", mload(/** @src 5:6923:6968  "numAssets = uint8(config.assetConfigs.length)" */ 832))
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            setimmutable(_48, "1340", mload(/** @src 5:5705:5758  "accrualDescaleFactor = baseScale / BASE_ACCRUAL_SCALE" */ 864))
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            setimmutable(_48, "1343", mload(/** @src 5:6979:7108  "assetList = IAssetListFactory(IAssetListFactoryHolder(extensionDelegate).assetListFactory()).createAssetList(config.assetConfigs)" */ 896))
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            return(_48, datasize("CometWithExtendedAssetList_4926_deployed"))
        }
        function finalize_allocation(memPtr, size)
        {
            let newFreePtr := add(memPtr, and(add(size, 31), not(31)))
            if or(gt(newFreePtr, sub(shl(64, 1), 1)), lt(newFreePtr, memPtr))
            {
                mstore(0, shl(224, 0x4e487b71))
                mstore(4, 0x41)
                revert(0, 0x24)
            }
            mstore(64, newFreePtr)
        }
        function abi_decode_address_fromMemory(offset) -> value
        {
            value := mload(offset)
            if iszero(eq(value, and(value, sub(shl(160, 1), 1)))) { revert(0, 0) }
        }
        function abi_decode_uint64_fromMemory(offset) -> value
        {
            value := mload(offset)
            if iszero(eq(value, and(value, sub(shl(64, 1), 1)))) { revert(0, 0) }
        }
        function abi_decode_uint104_fromMemory(offset) -> value
        {
            value := mload(offset)
            if iszero(eq(value, and(value, sub(shl(104, 1), 1)))) { revert(0, 0) }
        }
        function abi_decode_uint8_fromMemory(offset) -> value
        {
            value := mload(offset)
            if iszero(eq(value, and(value, 0xff))) { revert(0, 0) }
        }
    }
    /// @use-src 1:"CometCore.sol", 3:"CometMath.sol", 4:"CometStorage.sol", 5:"CometWithExtendedAssetList.sol"
    object "CometWithExtendedAssetList_4926_deployed" {
        code {
            {
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                mstore(64, 128)
                if iszero(lt(calldatasize(), 4))
                {
                    switch shr(224, calldataload(0))
                    case 0x042e02cf { external_fun_isLiquidatable() }
                    case 0x0902f1ac { external_fun_getReserves() }
                    case 0x0bc47ad1 { external_fun_isSupplyPaused() }
                    case 0x0c340a24 { external_fun_governor() }
                    case 0x18160ddd { external_fun_totalSupply() }
                    case 0x189bb2f1 {
                        external_fun_baseTrackingSupplySpeed()
                    }
                    case 0x1c9f7fb9 {
                        external_fun_initializeStorage()
                    }
                    case 0x1f5954bd {
                        external_fun_storeFrontPriceFactor()
                    }
                    case 0x23b872dd { external_fun_transferFrom() }
                    case 0x24a3d622 { external_fun_pauseGuardian() }
                    case 0x26441318 { external_fun_withdrawFrom() }
                    case 0x2a48cf12 {
                        external_fun_borrowPerSecondInterestRateSlopeHigh()
                    }
                    case 0x2b92a07d { external_fun_userCollateral() }
                    case 0x2d05670b {
                        external_fun_borrowPerSecondInterestRateSlopeLow()
                    }
                    case 0x2e04b8e7 { external_fun_userNonce() }
                    case 0x300e6beb { external_fun_baseBorrowMin() }
                    case 0x313ce567 { external_fun_decimals() }
                    case 0x32176c49 { external_fun_targetReserves() }
                    case 0x374c49b4 {
                        external_fun_borrowBalanceOf()
                    }
                    case 0x38aa813f {
                        external_fun_isBorrowCollateralized()
                    }
                    case 0x3b3bec2e {
                        external_fun_getAssetInfoByAddress()
                    }
                    case 0x41976e09 { external_fun_getPrice() }
                    case 0x4232cd63 { external_fun_supplyTo() }
                    case 0x439e2e45 { external_fun_transferAsset() }
                    case 0x44c1e5eb { external_fun_baseScale() }
                    case 0x44c35d07 { external_fun_pause() }
                    case 0x44ff241d {
                        external_fun_extensionDelegate()
                    }
                    case 0x59e017bd {
                        external_fun_totalsCollateral()
                    }
                    case 0x5a94b8d1 {
                        external_fun_supplyPerSecondInterestRateSlopeLow()
                    }
                    case 0x67800b5f {
                        external_fun_isWithdrawPaused()
                    }
                    case 0x70a08231 { external_fun_balanceOf() }
                    case 0x7914acc7 {
                        external_fun_borrowPerSecondInterestRateBase()
                    }
                    case 0x7ac88ed1 {
                        external_fun_quoteCollateral()
                    }
                    case 0x7eb71131 { external_fun_getUtilization() }
                    case 0x804de71f {
                        external_fun_supplyPerSecondInterestRateSlopeHigh()
                    }
                    case 0x8285ef40 { external_fun_totalBorrow() }
                    case 0x8d5d814c { external_fun_isAbsorbPaused() }
                    case 0x90323177 { external_fun_supplyFrom() }
                    case 0x9241a561 { external_fun_borrowKink() }
                    case 0x9364e18a {
                        external_fun_baseMinForRewards()
                    }
                    case 0x94920cca {
                        external_fun_supplyPerSecondInterestRateBase()
                    }
                    case 0x9ea99a5a {
                        external_fun_baseTrackingBorrowSpeed()
                    }
                    case 0x9fa83b5a { external_fun_getBorrowRate() }
                    case 0x9ff567f8 {
                        external_fun_getCollateralReserves()
                    }
                    case 0xa1654379 { external_fun_isAllowed() }
                    case 0xa1a1ef43 {
                        external_fun_isTransferPaused()
                    }
                    case 0xa46fe83b { external_fun_numAssets() }
                    case 0xa5b4ff79 { external_fun_supplyKink() }
                    case 0xa9059cbb { external_fun_transfer() }
                    case 0xaba7f15e {
                        external_fun_trackingIndexScale()
                    }
                    case 0xad14777c { external_fun_approveThis() }
                    case 0xbfe69c8d { external_fun_accrueAccount() }
                    case 0xc1ee2c18 {
                        external_fun_transferAssetFrom()
                    }
                    case 0xc3b35a7e { external_fun_withdrawTo() }
                    case 0xc3cecfd2 { external_fun_absorb() }
                    case 0xc55dae63 { external_fun_baseToken() }
                    case 0xc5fa15cf {
                        external_fun_liquidatorPoints()
                    }
                    case 0xc8c7fe6b { external_fun_getAssetInfo() }
                    case 0xcde68041 { external_fun_hasPermission() }
                    case 0xd8e5f611 { external_fun_isBuyPaused() }
                    case 0xd955759d { external_fun_getSupplyRate() }
                    case 0xdc4abafd { external_fun_userBasic() }
                    case 0xe372f03a { external_fun_assetList() }
                    case 0xe478795d {
                        external_fun_withdrawReserves()
                    }
                    case 0xe4e6e779 { external_fun_buyCollateral() }
                    case 0xe7dad6bd {
                        external_fun_baseTokenPriceFeed()
                    }
                    case 0xf2b9fdb8 { external_fun_supply() }
                    case 0xf3fef3a3 { external_fun_withdraw() }
                }
                fun()
            }
            function cleanup_address(value) -> cleaned
            {
                cleaned := and(value, sub(shl(160, 1), 1))
            }
            function validator_revert_address(value)
            {
                if iszero(eq(value, and(value, sub(shl(160, 1), 1)))) { revert(0, 0) }
            }
            function cleanup_bool(value) -> cleaned
            {
                cleaned := iszero(iszero(value))
            }
            function external_fun_isLiquidatable()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 32)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let value := calldataload(4)
                validator_revert_address(value)
                let ret := fun_isLiquidatable(value)
                let memPos := mload(64)
                mstore(memPos, iszero(iszero(ret)))
                return(memPos, 32)
            }
            function abi_decode(headStart, dataEnd)
            {
                if slt(sub(dataEnd, headStart), 0) { revert(0, 0) }
            }
            function external_fun_getReserves()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                let ret := fun_getReserves()
                let memPos := mload(64)
                mstore(memPos, ret)
                return(memPos, 32)
            }
            function external_fun_isSupplyPaused()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                let ret := /** @src 3:1636:1642  "x != 0" */ iszero(iszero(/** @src 5:20691:20737  "pauseFlags & (uint8(1) << PAUSE_SUPPLY_OFFSET)" */ and(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ shr(248, sload(/** @src 5:20691:20701  "pauseFlags" */ 0x01)), 0x01)))
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let memPos := mload(64)
                mstore(memPos, ret)
                return(memPos, 32)
            }
            function abi_encode_address(headStart, value0) -> tail
            {
                tail := add(headStart, 32)
                mstore(headStart, and(value0, sub(shl(160, 1), 1)))
            }
            function external_fun_governor()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                let memPos := mload(64)
                mstore(memPos, and(/** @src 5:587:629  "address public override immutable governor" */ loadimmutable("1249"), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(shl(160, 1), 1)))
                return(memPos, 32)
            }
            function abi_encode_uint256(headStart, value0) -> tail
            {
                tail := add(headStart, 32)
                mstore(headStart, value0)
            }
            function external_fun_totalSupply()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                /// @src 5:49316:49332  "getNowInternal()"
                let expr := fun_getNowInternal()
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _1 := sload(/** @src 5:49335:49350  "lastAccrualTime" */ 0x01)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _2 := 0xffffffffff
                /// @src 5:49293:49351  "accruedInterestIndices(getNowInternal() - lastAccrualTime)"
                let expr_component, expr_component_1 := fun_accruedInterestIndices(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:49316:49350  "getNowInternal() - lastAccrualTime" */ checked_sub_uint40(expr, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(shr(208, _1), _2)), _2))
                /// @src 5:49361:49421  "return presentValueSupply(baseSupplyIndex_, totalSupplyBase)"
                let var := /** @src 5:49368:49421  "presentValueSupply(baseSupplyIndex_, totalSupplyBase)" */ fun_presentValueSupply(expr_component, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(_1, sub(shl(104, 1), 1)))
                let memPos := mload(64)
                mstore(memPos, var)
                return(memPos, 32)
            }
            function external_fun_baseTrackingSupplySpeed()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                let memPos := mload(64)
                mstore(memPos, /** @src 5:3127:3181  "uint public override immutable baseTrackingSupplySpeed" */ loadimmutable("1313"))
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                return(memPos, 32)
            }
            function external_fun_initializeStorage()
            {
                if callvalue() { revert(0, 0) }
                let _1 := 0
                if slt(add(calldatasize(), not(3)), _1) { revert(_1, _1) }
                let _2 := sload(/** @src 5:8375:8390  "lastAccrualTime" */ 0x01)
                /// @src 5:8371:8424  "if (lastAccrualTime != 0) revert AlreadyInitialized()"
                if /** @src 5:8375:8395  "lastAccrualTime != 0" */ iszero(iszero(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(shr(208, _2), 0xffffffffff)))
                /// @src 5:8371:8424  "if (lastAccrualTime != 0) revert AlreadyInitialized()"
                {
                    /// @src 5:8404:8424  "AlreadyInitialized()"
                    let _3 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 5:8404:8424  "AlreadyInitialized()"
                    mstore(_3, shl(228, 14423199))
                    revert(_3, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 4)
                }
                sstore(/** @src 5:8375:8390  "lastAccrualTime" */ 0x01, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ or(and(_2, not(shl(208, 0xffffffffff))), and(shl(208, /** @src 5:8486:8502  "getNowInternal()" */ fun_getNowInternal()), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ shl(208, 0xffffffffff))))
                /// @src 1:1927:1931  "1e15"
                let _4 := sload(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1)
                /// @src 1:1927:1931  "1e15"
                sstore(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1, /** @src 1:1927:1931  "1e15" */ or(and(_4, not(sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1))), /** @src 1:1927:1931  "1e15" */ 0x038d7ea4c68000))
                sstore(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1, /** @src 1:1927:1931  "1e15" */ or(and(_4, not(sub(shl(128, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1))), /** @src 1:1927:1931  "1e15" */ 0x038d7ea4c6800000038d7ea4c68000))
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                return(mload(/** @src 1:1927:1931  "1e15" */ 64), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1)
            }
            function external_fun_storeFrontPriceFactor()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                let memPos := mload(64)
                mstore(memPos, /** @src 5:2700:2752  "uint public override immutable storeFrontPriceFactor" */ loadimmutable("1301"))
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                return(memPos, 32)
            }
            function abi_decode_addresst_addresst_uint256(headStart, dataEnd) -> value0, value1, value2
            {
                if slt(sub(dataEnd, headStart), 96) { revert(0, 0) }
                let value := calldataload(headStart)
                validator_revert_address(value)
                value0 := value
                let value_1 := calldataload(add(headStart, 32))
                validator_revert_address(value_1)
                value1 := value_1
                value2 := calldataload(add(headStart, 64))
            }
            function external_fun_transferFrom()
            {
                if callvalue() { revert(0, 0) }
                let param, param_1, param_2 := abi_decode_addresst_addresst_uint256(4, calldatasize())
                /// @src 5:7333:7434  "modifier nonReentrant() {..."
                fun_nonReentrantBefore()
                /// @src 5:7397:7398  "_"
                fun_transferInternal_inner(/** @src 5:32563:32573  "msg.sender" */ caller(), /** @src 5:7397:7398  "_" */ param, param_1, /** @src 5:32585:32594  "baseToken" */ loadimmutable("1257"), /** @src 5:7397:7398  "_" */ param_2)
                /// @src 5:8094:8185  "assembly (\"memory-safe\") {..."
                sstore(/** @src 1:2266:2301  "keccak256(\"comet.reentrancy.guard\")" */ 0xc98c7730ba19013824f711a9ab74801459b27e6ff7685cb924587c89aeda53ac, /** @src -1:-1:-1 */ 0)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let memPos := mload(64)
                mstore(memPos, /** @src 5:32620:32624  "true" */ 0x01)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                return(memPos, 32)
            }
            function external_fun_pauseGuardian()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                let memPos := mload(64)
                mstore(memPos, and(/** @src 5:689:736  "address public override immutable pauseGuardian" */ loadimmutable("1253"), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(shl(160, 1), 1)))
                return(memPos, 32)
            }
            function abi_decode_addresst_addresst_addresst_uint256(headStart, dataEnd) -> value0, value1, value2, value3
            {
                if slt(sub(dataEnd, headStart), 128) { revert(0, 0) }
                let value := calldataload(headStart)
                validator_revert_address(value)
                value0 := value
                let value_1 := calldataload(add(headStart, 32))
                validator_revert_address(value_1)
                value1 := value_1
                let value_2 := calldataload(add(headStart, 64))
                validator_revert_address(value_2)
                value2 := value_2
                value3 := calldataload(add(headStart, 96))
            }
            function external_fun_withdrawFrom()
            {
                if callvalue() { revert(0, 0) }
                let param, param_1, param_2, param_3 := abi_decode_addresst_addresst_addresst_uint256(4, calldatasize())
                /// @src 5:7333:7434  "modifier nonReentrant() {..."
                fun_nonReentrantBefore()
                /// @src 5:7397:7398  "_"
                fun_withdrawInternal_inner(/** @src 5:38059:38069  "msg.sender" */ caller(), /** @src 5:7397:7398  "_" */ param, param_1, param_2, param_3)
                /// @src 5:8094:8185  "assembly (\"memory-safe\") {..."
                sstore(/** @src 1:2266:2301  "keccak256(\"comet.reentrancy.guard\")" */ 0xc98c7730ba19013824f711a9ab74801459b27e6ff7685cb924587c89aeda53ac, /** @src -1:-1:-1 */ 0)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                return(mload(64), /** @src -1:-1:-1 */ 0)
            }
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            function external_fun_borrowPerSecondInterestRateSlopeHigh()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                let memPos := mload(64)
                mstore(memPos, /** @src 5:2341:2408  "uint public override immutable borrowPerSecondInterestRateSlopeHigh" */ loadimmutable("1293"))
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                return(memPos, 32)
            }
            function abi_decode_addresst_address(headStart, dataEnd) -> value0, value1
            {
                if slt(sub(dataEnd, headStart), 64) { revert(0, 0) }
                let value := calldataload(headStart)
                validator_revert_address(value)
                value0 := value
                let value_1 := calldataload(add(headStart, 32))
                validator_revert_address(value_1)
                value1 := value_1
            }
            function mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(slot, key) -> dataSlot
            {
                mstore(0, and(key, sub(shl(160, 1), 1)))
                mstore(0x20, slot)
                dataSlot := keccak256(0, 0x40)
            }
            function cleanup_from_storage_uint128(value) -> cleaned
            {
                cleaned := and(value, /** @src 1:1927:1931  "1e15" */ sub(shl(128, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1))
            }
            function read_from_storage_split_offset_uint128(slot) -> value
            {
                value := and(sload(slot), /** @src 1:1927:1931  "1e15" */ sub(shl(128, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1))
            }
            function abi_encode_uint128(value, pos)
            {
                mstore(pos, and(value, /** @src 1:1927:1931  "1e15" */ sub(shl(128, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)))
            }
            function abi_encode_uint128_uint128(headStart, value0, value1) -> tail
            {
                tail := add(headStart, 64)
                let _1 := /** @src 1:1927:1931  "1e15" */ sub(shl(128, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)
                mstore(headStart, and(value0, _1))
                mstore(add(headStart, 32), and(value1, _1))
            }
            function external_fun_userCollateral()
            {
                if callvalue() { revert(0, 0) }
                let param, param_1 := abi_decode_addresst_address(4, calldatasize())
                mstore(/** @src -1:-1:-1 */ 0, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(param, sub(shl(160, 1), 1)))
                mstore(0x20, /** @src 4:2117:2193  "mapping(address => mapping(address => UserCollateral)) public userCollateral" */ 6)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _1 := sload(/** @src 4:2117:2193  "mapping(address => mapping(address => UserCollateral)) public userCollateral" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ keccak256(/** @src -1:-1:-1 */ 0, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0x40), /** @src 4:2117:2193  "mapping(address => mapping(address => UserCollateral)) public userCollateral" */ param_1))
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let memPos := mload(0x40)
                return(memPos, sub(abi_encode_uint128_uint128(memPos, and(_1, /** @src 1:1927:1931  "1e15" */ sub(shl(128, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)), shr(128, _1)), memPos))
            }
            function external_fun_borrowPerSecondInterestRateSlopeLow()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                let memPos := mload(64)
                mstore(memPos, /** @src 5:2146:2212  "uint public override immutable borrowPerSecondInterestRateSlopeLow" */ loadimmutable("1289"))
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                return(memPos, 32)
            }
            function external_fun_userNonce()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 32)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let value := calldataload(4)
                validator_revert_address(value)
                mstore(/** @src -1:-1:-1 */ 0, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(value, sub(shl(160, 1), 1)))
                mstore(32, 4)
                let _1 := sload(keccak256(/** @src -1:-1:-1 */ 0, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0x40))
                let memPos := mload(0x40)
                mstore(memPos, _1)
                return(memPos, 32)
            }
            function external_fun_baseBorrowMin()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                let memPos := mload(64)
                mstore(memPos, /** @src 5:3693:3737  "uint public override immutable baseBorrowMin" */ loadimmutable("1325"))
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                return(memPos, 32)
            }
            function cleanup_uint8(value) -> cleaned
            { cleaned := and(value, 0xff) }
            function external_fun_decimals()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                let memPos := mload(64)
                mstore(memPos, and(/** @src 5:3953:3993  "uint8 public override immutable decimals" */ loadimmutable("1333"), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0xff))
                return(memPos, 32)
            }
            function external_fun_targetReserves()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                let memPos := mload(64)
                mstore(memPos, /** @src 5:3839:3884  "uint public override immutable targetReserves" */ loadimmutable("1329"))
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                return(memPos, 32)
            }
            function external_fun_borrowBalanceOf()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 32)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let value := calldataload(4)
                validator_revert_address(value)
                let ret := fun_borrowBalanceOf(value)
                let memPos := mload(64)
                mstore(memPos, ret)
                return(memPos, 32)
            }
            function external_fun_isBorrowCollateralized()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 32)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let value := calldataload(4)
                validator_revert_address(value)
                let ret := fun_isBorrowCollateralized(value)
                let memPos := mload(64)
                mstore(memPos, iszero(iszero(ret)))
                return(memPos, 32)
            }
            function cleanup_uint64(value) -> cleaned
            {
                cleaned := and(value, /** @src 1:1927:1931  "1e15" */ sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1))
            }
            function abi_encode_uint64(value, pos)
            {
                mstore(pos, and(value, /** @src 1:1927:1931  "1e15" */ sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)))
            }
            function abi_encode_struct_AssetInfo(headStart, value0) -> tail
            {
                tail := add(headStart, 256)
                mstore(headStart, and(mload(value0), 0xff))
                let memberValue0 := mload(add(value0, 0x20))
                let _1 := sub(shl(160, 1), 1)
                mstore(add(headStart, 0x20), and(memberValue0, _1))
                mstore(add(headStart, 0x40), and(mload(add(value0, 0x40)), _1))
                mstore(add(headStart, 0x60), and(mload(add(value0, 0x60)), /** @src 1:1927:1931  "1e15" */ sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)))
                let memberValue0_1 := mload(add(value0, 0x80))
                abi_encode_uint64(memberValue0_1, add(headStart, 0x80))
                let memberValue0_2 := mload(add(value0, 0xa0))
                abi_encode_uint64(memberValue0_2, add(headStart, 0xa0))
                let memberValue0_3 := mload(add(value0, 0xc0))
                abi_encode_uint64(memberValue0_3, add(headStart, 0xc0))
                let memberValue0_4 := mload(add(value0, 0xe0))
                abi_encode_uint128(memberValue0_4, add(headStart, 0xe0))
            }
            function external_fun_getAssetInfoByAddress()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 32)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let value := calldataload(4)
                validator_revert_address(value)
                let ret := fun_getAssetInfoByAddress(value)
                let memPos := mload(64)
                return(memPos, sub(abi_encode_struct_AssetInfo(memPos, ret), memPos))
            }
            function external_fun_getPrice()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 32)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let value := calldataload(4)
                validator_revert_address(value)
                let ret := fun_getPrice(value)
                let memPos := mload(64)
                mstore(memPos, ret)
                return(memPos, 32)
            }
            function external_fun_supplyTo()
            {
                if callvalue() { revert(0, 0) }
                let param, param_1, param_2 := abi_decode_addresst_addresst_uint256(4, calldatasize())
                /// @src 5:7333:7434  "modifier nonReentrant() {..."
                fun_nonReentrantBefore()
                /// @src 5:7397:7398  "_"
                fun_supplyInternal_inner(/** @src 5:28774:28784  "msg.sender" */ caller(), caller(), /** @src 5:7397:7398  "_" */ param, param_1, param_2)
                /// @src 5:8094:8185  "assembly (\"memory-safe\") {..."
                sstore(/** @src 1:2266:2301  "keccak256(\"comet.reentrancy.guard\")" */ 0xc98c7730ba19013824f711a9ab74801459b27e6ff7685cb924587c89aeda53ac, /** @src -1:-1:-1 */ 0)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                return(mload(64), /** @src -1:-1:-1 */ 0)
            }
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            function external_fun_transferAsset()
            {
                if callvalue() { revert(0, 0) }
                let param, param_1, param_2 := abi_decode_addresst_addresst_uint256(4, calldatasize())
                /// @src 5:7333:7434  "modifier nonReentrant() {..."
                fun_nonReentrantBefore()
                /// @src 5:7397:7398  "_"
                fun_transferInternal_inner(/** @src 5:32947:32957  "msg.sender" */ caller(), caller(), /** @src 5:7397:7398  "_" */ param, param_1, param_2)
                /// @src 5:8094:8185  "assembly (\"memory-safe\") {..."
                sstore(/** @src 1:2266:2301  "keccak256(\"comet.reentrancy.guard\")" */ 0xc98c7730ba19013824f711a9ab74801459b27e6ff7685cb924587c89aeda53ac, /** @src -1:-1:-1 */ 0)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                return(mload(64), /** @src -1:-1:-1 */ 0)
            }
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            function external_fun_baseScale()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                let memPos := mload(64)
                mstore(memPos, /** @src 5:2852:2892  "uint public override immutable baseScale" */ loadimmutable("1305"))
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                return(memPos, 32)
            }
            function abi_decode_bool(offset) -> value
            {
                value := calldataload(offset)
                if iszero(eq(value, iszero(iszero(value)))) { revert(0, 0) }
            }
            function external_fun_pause()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 160)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let value0 := abi_decode_bool(4)
                let value1 := abi_decode_bool(36)
                let value2 := abi_decode_bool(68)
                let value3 := abi_decode_bool(100)
                let value4 := abi_decode_bool(132)
                let _1 := sub(shl(160, 1), 1)
                /// @src 5:19995:20048  "msg.sender != governor && msg.sender != pauseGuardian"
                let expr := /** @src 5:19995:20017  "msg.sender != governor" */ iszero(eq(/** @src 5:19995:20005  "msg.sender" */ caller(), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:20009:20017  "governor" */ loadimmutable("1249"), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1)))
                /// @src 5:19995:20048  "msg.sender != governor && msg.sender != pauseGuardian"
                if expr
                {
                    expr := /** @src 5:20021:20048  "msg.sender != pauseGuardian" */ iszero(eq(/** @src 5:19995:20005  "msg.sender" */ caller(), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:20035:20048  "pauseGuardian" */ loadimmutable("1253"), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1)))
                }
                /// @src 5:19991:20071  "if (msg.sender != governor && msg.sender != pauseGuardian) revert Unauthorized()"
                if expr
                {
                    /// @src 5:20057:20071  "Unauthorized()"
                    let _2 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 5:20057:20071  "Unauthorized()"
                    mstore(_2, shl(232, 8565801))
                    revert(_2, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 4)
                }
                /// @src 5:20131:20175  "toUInt8(supplyPaused) << PAUSE_SUPPLY_OFFSET"
                let _3 := shift_left_uint8_uint8(/** @src 5:20131:20152  "toUInt8(supplyPaused)" */ fun_toUInt8(value0), /** @src -1:-1:-1 */ 0)
                /// @src 5:20107:20241  "uint8(0) |..."
                let expr_1 := or(_3, /** @src 5:20192:20240  "toUInt8(transferPaused) << PAUSE_TRANSFER_OFFSET" */ shift_left_uint8_uint8(/** @src 5:20192:20215  "toUInt8(transferPaused)" */ fun_toUInt8(value1), /** @src 1:1302:1303  "1" */ 0x01))
                /// @src 5:20107:20306  "uint8(0) |..."
                let expr_2 := or(expr_1, /** @src 5:20257:20305  "toUInt8(withdrawPaused) << PAUSE_WITHDRAW_OFFSET" */ shift_left_uint8_uint8(/** @src 5:20257:20280  "toUInt8(withdrawPaused)" */ fun_toUInt8(value2), /** @src 1:1357:1358  "2" */ 0x02))
                /// @src 5:20107:20367  "uint8(0) |..."
                let expr_3 := or(expr_2, /** @src 5:20322:20366  "toUInt8(absorbPaused) << PAUSE_ABSORB_OFFSET" */ shift_left_uint8_uint8(/** @src 5:20322:20343  "toUInt8(absorbPaused)" */ fun_toUInt8(value3), /** @src 1:1410:1411  "3" */ 0x03))
                /// @src 5:20082:20422  "pauseFlags =..."
                update_storage_value_offsett_uint8_to_uint8(/** @src 1:1302:1303  "1" */ 0x01, /** @src 5:20107:20422  "uint8(0) |..." */ or(expr_3, /** @src 5:20383:20421  "toUInt8(buyPaused) << PAUSE_BUY_OFFSET" */ shift_left_uint8_uint8(/** @src 5:20383:20401  "toUInt8(buyPaused)" */ fun_toUInt8(value4), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 4)))
                /// @src 5:20438:20520  "PauseAction(supplyPaused, transferPaused, withdrawPaused, absorbPaused, buyPaused)"
                let _4 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                /// @src 5:20438:20520  "PauseAction(supplyPaused, transferPaused, withdrawPaused, absorbPaused, buyPaused)"
                log1(_4, sub(abi_encode_bool_bool_bool_bool_bool(_4, value0, value1, value2, value3, value4), _4), 0x3be39979091ae7ca962aa1c44e645f2df3c221b79f324afa5f44aedc8d2f690d)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                return(mload(64), /** @src -1:-1:-1 */ 0)
            }
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            function external_fun_extensionDelegate()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                let memPos := mload(64)
                mstore(memPos, and(/** @src 5:1035:1086  "address public override immutable extensionDelegate" */ loadimmutable("1265"), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(shl(160, 1), 1)))
                return(memPos, 32)
            }
            function external_fun_totalsCollateral()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 32)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let value := calldataload(4)
                validator_revert_address(value)
                mstore(/** @src -1:-1:-1 */ 0, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(value, sub(shl(160, 1), 1)))
                mstore(32, /** @src 4:1541:1601  "mapping(address => TotalsCollateral) public totalsCollateral" */ 2)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _1 := sload(keccak256(/** @src -1:-1:-1 */ 0, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0x40))
                let memPos := mload(0x40)
                return(memPos, sub(abi_encode_uint128_uint128(memPos, and(_1, /** @src 1:1927:1931  "1e15" */ sub(shl(128, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)), shr(128, _1)), memPos))
            }
            function external_fun_supplyPerSecondInterestRateSlopeLow()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                let memPos := mload(64)
                mstore(memPos, /** @src 5:1410:1476  "uint public override immutable supplyPerSecondInterestRateSlopeLow" */ loadimmutable("1273"))
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                return(memPos, 32)
            }
            function external_fun_isWithdrawPaused()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                let ret := /** @src 3:1636:1642  "x != 0" */ iszero(iszero(/** @src 5:21137:21185  "pauseFlags & (uint8(1) << PAUSE_WITHDRAW_OFFSET)" */ and(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ shr(248, sload(/** @src 5:21137:21147  "pauseFlags" */ 0x01)), /** @src 1:1247:1248  "0" */ 4)))
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let memPos := mload(64)
                mstore(memPos, ret)
                return(memPos, 32)
            }
            function external_fun_balanceOf()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 32)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let value := calldataload(4)
                validator_revert_address(value)
                let ret := fun_balanceOf(value)
                let memPos := mload(64)
                mstore(memPos, ret)
                return(memPos, 32)
            }
            function external_fun_borrowPerSecondInterestRateBase()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                let memPos := mload(64)
                mstore(memPos, /** @src 5:2497:2559  "uint public override immutable borrowPerSecondInterestRateBase" */ loadimmutable("1297"))
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                return(memPos, 32)
            }
            function external_fun_quoteCollateral()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 64)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let value := calldataload(4)
                validator_revert_address(value)
                let ret := fun_quoteCollateral(value, calldataload(36))
                let memPos := mload(64)
                mstore(memPos, ret)
                return(memPos, 32)
            }
            function external_fun_getUtilization()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                let ret := fun_getUtilization()
                let memPos := mload(64)
                mstore(memPos, ret)
                return(memPos, 32)
            }
            function external_fun_supplyPerSecondInterestRateSlopeHigh()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                let memPos := mload(64)
                mstore(memPos, /** @src 5:1605:1672  "uint public override immutable supplyPerSecondInterestRateSlopeHigh" */ loadimmutable("1277"))
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                return(memPos, 32)
            }
            function external_fun_totalBorrow()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                /// @src 5:49717:49733  "getNowInternal()"
                let expr := fun_getNowInternal()
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _1 := sload(/** @src 5:49736:49751  "lastAccrualTime" */ 0x01)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _2 := 0xffffffffff
                /// @src 5:49694:49752  "accruedInterestIndices(getNowInternal() - lastAccrualTime)"
                let expr_component, expr_component_1 := fun_accruedInterestIndices(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:49717:49751  "getNowInternal() - lastAccrualTime" */ checked_sub_uint40(expr, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(shr(208, _1), _2)), _2))
                /// @src 5:49762:49822  "return presentValueBorrow(baseBorrowIndex_, totalBorrowBase)"
                let var := /** @src 5:49769:49822  "presentValueBorrow(baseBorrowIndex_, totalBorrowBase)" */ fun_presentValueSupply(expr_component_1, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(shr(104, _1), sub(shl(104, 1), 1)))
                let memPos := mload(64)
                mstore(memPos, var)
                return(memPos, 32)
            }
            function external_fun_isAbsorbPaused()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                let ret := /** @src 3:1636:1642  "x != 0" */ iszero(iszero(/** @src 5:21357:21403  "pauseFlags & (uint8(1) << PAUSE_ABSORB_OFFSET)" */ and(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ shr(248, sload(/** @src 5:21357:21367  "pauseFlags" */ 0x01)), /** @src 1:1247:1248  "0" */ 8)))
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let memPos := mload(64)
                mstore(memPos, ret)
                return(memPos, 32)
            }
            function external_fun_supplyFrom()
            {
                if callvalue() { revert(0, 0) }
                let param, param_1, param_2, param_3 := abi_decode_addresst_addresst_addresst_uint256(4, calldatasize())
                /// @src 5:7333:7434  "modifier nonReentrant() {..."
                fun_nonReentrantBefore()
                /// @src 5:7397:7398  "_"
                fun_supplyInternal_inner(/** @src 5:29225:29235  "msg.sender" */ caller(), /** @src 5:7397:7398  "_" */ param, param_1, param_2, param_3)
                /// @src 5:8094:8185  "assembly (\"memory-safe\") {..."
                sstore(/** @src 1:2266:2301  "keccak256(\"comet.reentrancy.guard\")" */ 0xc98c7730ba19013824f711a9ab74801459b27e6ff7685cb924587c89aeda53ac, /** @src -1:-1:-1 */ 0)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                return(mload(64), /** @src -1:-1:-1 */ 0)
            }
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            function external_fun_borrowKink()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                let memPos := mload(64)
                mstore(memPos, /** @src 5:1976:2017  "uint public override immutable borrowKink" */ loadimmutable("1285"))
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                return(memPos, 32)
            }
            function external_fun_baseMinForRewards()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                let memPos := mload(64)
                mstore(memPos, /** @src 5:3568:3616  "uint public override immutable baseMinForRewards" */ loadimmutable("1321"))
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                return(memPos, 32)
            }
            function external_fun_supplyPerSecondInterestRateBase()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                let memPos := mload(64)
                mstore(memPos, /** @src 5:1761:1823  "uint public override immutable supplyPerSecondInterestRateBase" */ loadimmutable("1281"))
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                return(memPos, 32)
            }
            function external_fun_baseTrackingBorrowSpeed()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                let memPos := mload(64)
                mstore(memPos, /** @src 5:3294:3348  "uint public override immutable baseTrackingBorrowSpeed" */ loadimmutable("1317"))
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                return(memPos, 32)
            }
            function external_fun_getBorrowRate()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 32)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let ret := fun_getBorrowRate(calldataload(4))
                let memPos := mload(64)
                mstore(memPos, and(ret, /** @src 1:1927:1931  "1e15" */ sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)))
                return(memPos, 32)
            }
            function external_fun_getCollateralReserves()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 32)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let value := calldataload(4)
                validator_revert_address(value)
                let ret := fun_getCollateralReserves(value)
                let memPos := mload(64)
                mstore(memPos, ret)
                return(memPos, 32)
            }
            function external_fun_isAllowed()
            {
                if callvalue() { revert(0, 0) }
                let param, param_1 := abi_decode_addresst_address(4, calldatasize())
                mstore(/** @src 4:1703:1764  "mapping(address => mapping(address => bool)) public isAllowed" */ 0, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(param, sub(shl(160, 1), 1)))
                mstore(0x20, /** @src 4:1703:1764  "mapping(address => mapping(address => bool)) public isAllowed" */ 3)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let value := and(sload(/** @src 4:1703:1764  "mapping(address => mapping(address => bool)) public isAllowed" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ keccak256(/** @src 4:1703:1764  "mapping(address => mapping(address => bool)) public isAllowed" */ 0, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0x40), param_1)), 0xff)
                let memPos := mload(0x40)
                mstore(memPos, iszero(iszero(value)))
                return(memPos, 0x20)
            }
            function external_fun_isTransferPaused()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                let ret := /** @src 3:1636:1642  "x != 0" */ iszero(iszero(/** @src 5:20913:20961  "pauseFlags & (uint8(1) << PAUSE_TRANSFER_OFFSET)" */ and(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ shr(248, sload(/** @src 5:20913:20923  "pauseFlags" */ 0x01)), /** @src 1:1247:1248  "0" */ 2)))
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let memPos := mload(64)
                mstore(memPos, ret)
                return(memPos, 32)
            }
            function external_fun_numAssets()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                let memPos := mload(64)
                mstore(memPos, and(/** @src 5:4069:4110  "uint8 public override immutable numAssets" */ loadimmutable("1337"), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0xff))
                return(memPos, 32)
            }
            function external_fun_supplyKink()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                let memPos := mload(64)
                mstore(memPos, /** @src 5:1240:1281  "uint public override immutable supplyKink" */ loadimmutable("1269"))
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                return(memPos, 32)
            }
            function external_fun_transfer()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 64)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let value := calldataload(4)
                validator_revert_address(value)
                /// @src 5:7333:7434  "modifier nonReentrant() {..."
                fun_nonReentrantBefore()
                /// @src 5:7397:7398  "_"
                fun_transferInternal_inner(/** @src 5:32120:32130  "msg.sender" */ caller(), caller(), /** @src 5:7397:7398  "_" */ value, /** @src 5:32149:32158  "baseToken" */ loadimmutable("1257"), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ calldataload(36))
                /// @src 5:8094:8185  "assembly (\"memory-safe\") {..."
                sstore(/** @src 1:2266:2301  "keccak256(\"comet.reentrancy.guard\")" */ 0xc98c7730ba19013824f711a9ab74801459b27e6ff7685cb924587c89aeda53ac, /** @src -1:-1:-1 */ 0)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let memPos := mload(64)
                mstore(memPos, /** @src 5:32184:32188  "true" */ 0x01)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                return(memPos, 32)
            }
            function external_fun_trackingIndexScale()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                let memPos := mload(64)
                mstore(memPos, /** @src 5:2965:3014  "uint public override immutable trackingIndexScale" */ loadimmutable("1309"))
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                return(memPos, 32)
            }
            function external_fun_approveThis()
            {
                if callvalue() { revert(0, 0) }
                let param, param_1, param_2 := abi_decode_addresst_addresst_uint256(4, calldatasize())
                let _1 := sub(shl(160, 1), 1)
                /// @src 5:48892:48941  "if (msg.sender != governor) revert Unauthorized()"
                if /** @src 5:48896:48918  "msg.sender != governor" */ iszero(eq(/** @src 5:48896:48906  "msg.sender" */ caller(), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:48910:48918  "governor" */ loadimmutable("1249"), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1)))
                /// @src 5:48892:48941  "if (msg.sender != governor) revert Unauthorized()"
                {
                    /// @src 5:48927:48941  "Unauthorized()"
                    let _2 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 5:48927:48941  "Unauthorized()"
                    mstore(_2, /** @src 5:20057:20071  "Unauthorized()" */ shl(232, 8565801))
                    /// @src 5:48927:48941  "Unauthorized()"
                    revert(_2, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 4)
                }
                let _3 := and(/** @src 5:48952:48976  "IERC20NonStandard(asset)" */ param_1, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1)
                /// @src 5:48952:49001  "IERC20NonStandard(asset).approve(manager, amount)"
                if iszero(extcodesize(_3))
                {
                    /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                    revert(0, 0)
                }
                /// @src 5:48952:49001  "IERC20NonStandard(asset).approve(manager, amount)"
                let _4 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                /// @src 5:48952:49001  "IERC20NonStandard(asset).approve(manager, amount)"
                mstore(_4, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ shl(224, 0x095ea7b3))
                /// @src 5:48952:49001  "IERC20NonStandard(asset).approve(manager, amount)"
                let _5 := call(gas(), _3, 0, _4, sub(abi_encode_address_uint256(add(_4, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 4), /** @src 5:48952:49001  "IERC20NonStandard(asset).approve(manager, amount)" */ param, param_2), _4), _4, 0)
                if iszero(_5) { revert_forward() }
                if _5
                {
                    finalize_allocation(_4, 0)
                    abi_decode(_4, _4)
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                return(mload(64), /** @src 5:48952:49001  "IERC20NonStandard(asset).approve(manager, amount)" */ 0)
            }
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            function external_fun_accrueAccount()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 32)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let value := calldataload(4)
                validator_revert_address(value)
                /// @src 5:11379:11586  "function accrueAccount(address account) override external {..."
                fun_accrueInternal()
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                mstore(/** @src -1:-1:-1 */ 0, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(value, sub(shl(160, 1), 1)))
                mstore(32, /** @src 5:11499:11508  "userBasic" */ 0x05)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let dataSlot := keccak256(/** @src -1:-1:-1 */ 0, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0x40)
                let memPtr := mload(0x40)
                finalize_allocation(memPtr, 160)
                let _1 := sload(dataSlot)
                mstore(memPtr, signextend(12, _1))
                let _2 := /** @src 1:1927:1931  "1e15" */ sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)
                mstore(add(memPtr, 32), and(shr(104, _1), _2))
                mstore(add(memPtr, 0x40), and(shr(168, _1), _2))
                write_to_memory_uint16(add(memPtr, 96), and(shr(232, _1), 0xffff))
                write_to_memory_uint8(add(memPtr, 128), shr(248, _1))
                /// @src 5:11563:11578  "basic.principal"
                fun_updateBasePrincipal(value, memPtr, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_from_storage_int104(mload(/** @src 5:11563:11578  "basic.principal" */ memPtr)))
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                return(mload(0x40), /** @src -1:-1:-1 */ 0)
            }
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            function external_fun_transferAssetFrom()
            {
                if callvalue() { revert(0, 0) }
                let param, param_1, param_2, param_3 := abi_decode_addresst_addresst_addresst_uint256(4, calldatasize())
                /// @src 5:7333:7434  "modifier nonReentrant() {..."
                fun_nonReentrantBefore()
                /// @src 5:7397:7398  "_"
                fun_transferInternal_inner(/** @src 5:33388:33398  "msg.sender" */ caller(), /** @src 5:7397:7398  "_" */ param, param_1, param_2, param_3)
                /// @src 5:8094:8185  "assembly (\"memory-safe\") {..."
                sstore(/** @src 1:2266:2301  "keccak256(\"comet.reentrancy.guard\")" */ 0xc98c7730ba19013824f711a9ab74801459b27e6ff7685cb924587c89aeda53ac, /** @src -1:-1:-1 */ 0)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                return(mload(64), /** @src -1:-1:-1 */ 0)
            }
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            function external_fun_withdrawTo()
            {
                if callvalue() { revert(0, 0) }
                let param, param_1, param_2 := abi_decode_addresst_addresst_uint256(4, calldatasize())
                /// @src 5:7333:7434  "modifier nonReentrant() {..."
                fun_nonReentrantBefore()
                /// @src 5:7397:7398  "_"
                fun_withdrawInternal_inner(/** @src 5:37625:37635  "msg.sender" */ caller(), caller(), /** @src 5:7397:7398  "_" */ param, param_1, param_2)
                /// @src 5:8094:8185  "assembly (\"memory-safe\") {..."
                sstore(/** @src 1:2266:2301  "keccak256(\"comet.reentrancy.guard\")" */ 0xc98c7730ba19013824f711a9ab74801459b27e6ff7685cb924587c89aeda53ac, /** @src -1:-1:-1 */ 0)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                return(mload(64), /** @src -1:-1:-1 */ 0)
            }
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            function external_fun_absorb()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 64)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let value := calldataload(4)
                validator_revert_address(value)
                let offset := calldataload(36)
                let _1 := /** @src 1:1927:1931  "1e15" */ sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)
                if gt(offset, _1)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                if iszero(slt(add(offset, 35), calldatasize()))
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let length := calldataload(add(4, offset))
                if gt(length, _1)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                if gt(add(add(offset, shl(5, length)), 36), calldatasize())
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                fun_absorb(value, add(offset, 36), length)
                return(mload(64), /** @src -1:-1:-1 */ 0)
            }
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            function external_fun_baseToken()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                let memPos := mload(64)
                mstore(memPos, and(/** @src 5:798:841  "address public override immutable baseToken" */ loadimmutable("1257"), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(shl(160, 1), 1)))
                return(memPos, 32)
            }
            function cleanup_from_storage_uint32(value) -> cleaned
            {
                cleaned := and(value, 0xffffffff)
            }
            function external_fun_liquidatorPoints()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 32)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let value := calldataload(4)
                validator_revert_address(value)
                mstore(/** @src -1:-1:-1 */ 0, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(value, sub(shl(160, 1), 1)))
                mstore(32, /** @src 4:2251:2311  "mapping(address => LiquidatorPoints) public liquidatorPoints" */ 7)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _1 := sload(keccak256(/** @src -1:-1:-1 */ 0, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0x40))
                let memPos := mload(0x40)
                mstore(memPos, and(_1, 0xffffffff))
                mstore(add(memPos, 32), and(shr(32, _1), /** @src 1:1927:1931  "1e15" */ sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)))
                mstore(add(memPos, 0x40), and(shr(96, _1), /** @src 1:1927:1931  "1e15" */ sub(shl(128, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)))
                mstore(add(memPos, 96), shr(224, _1))
                return(memPos, 128)
            }
            function validator_revert_uint8(value)
            {
                if iszero(eq(value, and(value, 0xff))) { revert(0, 0) }
            }
            function external_fun_getAssetInfo()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 32)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let value := calldataload(4)
                validator_revert_uint8(value)
                let ret := fun_getAssetInfo(value)
                let memPos := mload(64)
                return(memPos, sub(abi_encode_struct_AssetInfo(memPos, ret), memPos))
            }
            function external_fun_hasPermission()
            {
                if callvalue() { revert(0, 0) }
                let param, param_1 := abi_decode_addresst_address(4, calldatasize())
                let ret := fun_hasPermission(param, param_1)
                let memPos := mload(64)
                mstore(memPos, iszero(iszero(ret)))
                return(memPos, 32)
            }
            function external_fun_isBuyPaused()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                let ret := /** @src 3:1636:1642  "x != 0" */ iszero(iszero(/** @src 5:21569:21612  "pauseFlags & (uint8(1) << PAUSE_BUY_OFFSET)" */ and(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ shr(248, sload(/** @src 5:21569:21579  "pauseFlags" */ 0x01)), /** @src 1:1247:1248  "0" */ 16)))
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let memPos := mload(64)
                mstore(memPos, ret)
                return(memPos, 32)
            }
            function external_fun_getSupplyRate()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 32)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let ret := fun_getSupplyRate(calldataload(4))
                let memPos := mload(64)
                mstore(memPos, and(ret, /** @src 1:1927:1931  "1e15" */ sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)))
                return(memPos, 32)
            }
            function cleanup_from_storage_int104(value) -> cleaned
            {
                cleaned := signextend(12, value)
            }
            function read_from_storage_split_offset_int104(slot) -> value
            {
                value := signextend(12, sload(slot))
            }
            function cleanup_from_storage_uint16(value) -> cleaned
            { cleaned := and(value, 0xffff) }
            function extract_from_storage_value_offsett_uint16(slot_value) -> value
            {
                value := and(shr(232, slot_value), 0xffff)
            }
            function read_from_storage_split_offset_uint16(slot) -> value
            {
                value := and(shr(232, sload(slot)), 0xffff)
            }
            function extract_from_storage_value_offsett_uint8(slot_value) -> value
            { value := shr(248, slot_value) }
            function read_from_storage_split_offset_uint8(slot) -> value
            {
                value := shr(248, sload(slot))
            }
            function external_fun_userBasic()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 32)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let value := calldataload(4)
                validator_revert_address(value)
                mstore(/** @src -1:-1:-1 */ 0, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(value, sub(shl(160, 1), 1)))
                mstore(32, /** @src 4:1991:2037  "mapping(address => UserBasic) public userBasic" */ 5)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _1 := sload(keccak256(/** @src -1:-1:-1 */ 0, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0x40))
                let _2 := /** @src 1:1927:1931  "1e15" */ sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)
                let memPos := mload(0x40)
                mstore(memPos, signextend(12, _1))
                mstore(add(memPos, 32), and(shr(104, _1), _2))
                mstore(add(memPos, 0x40), and(shr(168, _1), _2))
                mstore(add(memPos, 96), and(shr(232, _1), 0xffff))
                mstore(add(memPos, 128), shr(248, _1))
                return(memPos, 160)
            }
            function external_fun_assetList()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                let memPos := mload(64)
                mstore(memPos, and(/** @src 5:4331:4365  "address immutable public assetList" */ loadimmutable("1343"), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(shl(160, 1), 1)))
                return(memPos, 32)
            }
            function external_fun_withdrawReserves()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 64)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let value := calldataload(4)
                validator_revert_address(value)
                let value1 := calldataload(36)
                let _1 := sub(shl(160, 1), 1)
                /// @src 5:47938:47987  "if (msg.sender != governor) revert Unauthorized()"
                if /** @src 5:47942:47964  "msg.sender != governor" */ iszero(eq(/** @src 5:47942:47952  "msg.sender" */ caller(), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:47956:47964  "governor" */ loadimmutable("1249"), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1)))
                /// @src 5:47938:47987  "if (msg.sender != governor) revert Unauthorized()"
                {
                    /// @src 5:47973:47987  "Unauthorized()"
                    let _2 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 5:47973:47987  "Unauthorized()"
                    mstore(_2, /** @src 5:20057:20071  "Unauthorized()" */ shl(232, 8565801))
                    /// @src 5:47973:47987  "Unauthorized()"
                    revert(_2, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 4)
                }
                /// @src 5:48013:48026  "getReserves()"
                let expr := fun_getReserves()
                /// @src 5:48040:48086  "reserves < 0 || amount > unsigned256(reserves)"
                let expr_1 := /** @src 5:48040:48052  "reserves < 0" */ slt(expr, /** @src -1:-1:-1 */ 0)
                /// @src 5:48040:48086  "reserves < 0 || amount > unsigned256(reserves)"
                if iszero(expr_1)
                {
                    expr_1 := /** @src 5:48056:48086  "amount > unsigned256(reserves)" */ gt(value1, /** @src 5:48065:48086  "unsigned256(reserves)" */ fun_unsigned256(expr))
                }
                /// @src 5:48036:48117  "if (reserves < 0 || amount > unsigned256(reserves)) revert InsufficientReserves()"
                if expr_1
                {
                    /// @src 5:48095:48117  "InsufficientReserves()"
                    let _3 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 5:48095:48117  "InsufficientReserves()"
                    mstore(_3, shl(227, 0x128bd24d))
                    revert(_3, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 4)
                }
                /// @src 5:48157:48163  "amount"
                fun_doTransferOut(/** @src 5:48142:48151  "baseToken" */ loadimmutable("1257"), /** @src 5:48157:48163  "amount" */ value, value1)
                /// @src 5:48180:48208  "WithdrawReserves(to, amount)"
                let _4 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                /// @src 5:48180:48208  "WithdrawReserves(to, amount)"
                log2(_4, sub(abi_encode_uint256(_4, value1), _4), 0xec4431f2ba1a9382f6b0c4352b888cba6f7db91667d9f776abe5ad8ddc5401b6, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:48180:48208  "WithdrawReserves(to, amount)" */ value, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1))
                return(mload(64), /** @src -1:-1:-1 */ 0)
            }
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            function external_fun_buyCollateral()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 128)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let value := calldataload(4)
                validator_revert_address(value)
                let value_1 := calldataload(100)
                validator_revert_address(value_1)
                /// @src 5:7333:7434  "modifier nonReentrant() {..."
                fun_nonReentrantBefore()
                /// @src 5:45294:45328  "if (isBuyPaused()) revert Paused()"
                if /** @src 3:1636:1642  "x != 0" */ iszero(iszero(/** @src 5:21569:21612  "pauseFlags & (uint8(1) << PAUSE_BUY_OFFSET)" */ and(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ shr(248, sload(/** @src 5:21569:21579  "pauseFlags" */ 0x01)), /** @src 1:1247:1248  "0" */ 16)))
                /// @src 5:45294:45328  "if (isBuyPaused()) revert Paused()"
                {
                    /// @src 5:45320:45328  "Paused()"
                    let _1 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 5:45320:45328  "Paused()"
                    mstore(_1, shl(227, 0x13d0ff59))
                    revert(_1, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 4)
                }
                /// @src 5:45354:45367  "getReserves()"
                let expr := fun_getReserves()
                /// @src 5:45381:45430  "reserves >= 0 && uint(reserves) >= targetReserves"
                let expr_1 := /** @src 5:45381:45394  "reserves >= 0" */ iszero(slt(expr, /** @src -1:-1:-1 */ 0))
                /// @src 5:45381:45430  "reserves >= 0 && uint(reserves) >= targetReserves"
                if expr_1
                {
                    expr_1 := /** @src 5:45398:45430  "uint(reserves) >= targetReserves" */ iszero(lt(expr, /** @src 5:45416:45430  "targetReserves" */ loadimmutable("1329")))
                }
                /// @src 5:45377:45451  "if (reserves >= 0 && uint(reserves) >= targetReserves) revert NotForSale()"
                if expr_1
                {
                    /// @src 5:45439:45451  "NotForSale()"
                    let _2 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 5:45439:45451  "NotForSale()"
                    mstore(_2, shl(224, 0x1d99ddbf))
                    revert(_2, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 4)
                }
                /// @src 5:45570:45617  "doTransferIn(baseToken, msg.sender, baseAmount)"
                let expr_2 := fun_doTransferIn(/** @src 5:45583:45592  "baseToken" */ loadimmutable("1257"), /** @src 5:45594:45604  "msg.sender" */ caller(), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ calldataload(68))
                /// @src 5:45652:45686  "quoteCollateral(asset, baseAmount)"
                let expr_3 := fun_quoteCollateral(value, expr_2)
                /// @src 5:45696:45754  "if (collateralAmount < minAmount) revert TooMuchSlippage()"
                if /** @src 5:45700:45728  "collateralAmount < minAmount" */ lt(expr_3, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ calldataload(36))
                /// @src 5:45696:45754  "if (collateralAmount < minAmount) revert TooMuchSlippage()"
                {
                    /// @src 5:45737:45754  "TooMuchSlippage()"
                    let _3 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 5:45737:45754  "TooMuchSlippage()"
                    mstore(_3, shl(224, 0xfa6ad355))
                    revert(_3, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 4)
                }
                /// @src 5:45764:45846  "if (collateralAmount > getCollateralReserves(asset)) revert InsufficientReserves()"
                if /** @src 5:45768:45815  "collateralAmount > getCollateralReserves(asset)" */ gt(expr_3, /** @src 5:45787:45815  "getCollateralReserves(asset)" */ fun_getCollateralReserves(value))
                /// @src 5:45764:45846  "if (collateralAmount > getCollateralReserves(asset)) revert InsufficientReserves()"
                {
                    /// @src 5:45824:45846  "InsufficientReserves()"
                    let _4 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 5:45824:45846  "InsufficientReserves()"
                    mstore(_4, /** @src 5:48095:48117  "InsufficientReserves()" */ shl(227, 0x128bd24d))
                    /// @src 5:45824:45846  "InsufficientReserves()"
                    revert(_4, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 4)
                }
                /// @src 5:46192:46250  "doTransferOut(asset, recipient, safe128(collateralAmount))"
                fun_doTransferOut(value, value_1, cleanup_from_storage_uint128(/** @src 5:46224:46249  "safe128(collateralAmount)" */ fun_safe128(expr_3)))
                /// @src 5:46266:46328  "BuyCollateral(msg.sender, asset, baseAmount, collateralAmount)"
                let _5 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                /// @src 5:46266:46328  "BuyCollateral(msg.sender, asset, baseAmount, collateralAmount)"
                log3(_5, sub(abi_encode_uint256_uint256(_5, expr_2, expr_3), _5), 0xf891b2a411b0e66a5f0a6ff1368670fefa287a13f541eb633a386a1a9cc7046b, /** @src 5:45594:45604  "msg.sender" */ caller(), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:46266:46328  "BuyCollateral(msg.sender, asset, baseAmount, collateralAmount)" */ value, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(shl(160, 1), 1)))
                /// @src 5:7397:7398  "_"
                fun_nonReentrantAfter()
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                return(mload(64), /** @src -1:-1:-1 */ 0)
            }
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            function external_fun_baseTokenPriceFeed()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                let memPos := mload(64)
                mstore(memPos, and(/** @src 5:913:965  "address public override immutable baseTokenPriceFeed" */ loadimmutable("1261"), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(shl(160, 1), 1)))
                return(memPos, 32)
            }
            function external_fun_supply()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 64)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let value := calldataload(4)
                validator_revert_address(value)
                /// @src 5:7333:7434  "modifier nonReentrant() {..."
                fun_nonReentrantBefore()
                /// @src 5:7397:7398  "_"
                fun_supplyInternal_inner(/** @src 5:28396:28406  "msg.sender" */ caller(), caller(), caller(), /** @src 5:7397:7398  "_" */ value, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ calldataload(36))
                /// @src 5:8094:8185  "assembly (\"memory-safe\") {..."
                sstore(/** @src 1:2266:2301  "keccak256(\"comet.reentrancy.guard\")" */ 0xc98c7730ba19013824f711a9ab74801459b27e6ff7685cb924587c89aeda53ac, /** @src -1:-1:-1 */ 0)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                return(mload(64), /** @src -1:-1:-1 */ 0)
            }
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            function external_fun_withdraw()
            {
                if callvalue() { revert(0, 0) }
                if slt(add(calldatasize(), not(3)), 64)
                {
                    revert(/** @src -1:-1:-1 */ 0, 0)
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let value := calldataload(4)
                validator_revert_address(value)
                /// @src 5:7333:7434  "modifier nonReentrant() {..."
                fun_nonReentrantBefore()
                /// @src 5:7397:7398  "_"
                fun_withdrawInternal_inner(/** @src 5:37256:37266  "msg.sender" */ caller(), caller(), caller(), /** @src 5:7397:7398  "_" */ value, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ calldataload(36))
                /// @src 5:8094:8185  "assembly (\"memory-safe\") {..."
                sstore(/** @src 1:2266:2301  "keccak256(\"comet.reentrancy.guard\")" */ 0xc98c7730ba19013824f711a9ab74801459b27e6ff7685cb924587c89aeda53ac, /** @src -1:-1:-1 */ 0)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                return(mload(64), /** @src -1:-1:-1 */ 0)
            }
            /// @ast-id 190 @src 1:2715:2866  "function hasPermission(address owner, address manager) public view returns (bool) {..."
            function fun_hasPermission(var_owner, var_manager) -> var
            {
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _1 := sub(shl(160, 1), 1)
                let _2 := and(/** @src 1:2814:2830  "owner == manager" */ var_owner, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1)
                /// @src 1:2814:2859  "owner == manager || isAllowed[owner][manager]"
                let expr := /** @src 1:2814:2830  "owner == manager" */ eq(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _2, and(/** @src 1:2814:2830  "owner == manager" */ var_manager, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1))
                /// @src 1:2814:2859  "owner == manager || isAllowed[owner][manager]"
                if iszero(expr)
                {
                    /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                    mstore(/** @src -1:-1:-1 */ 0, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _2)
                    mstore(0x20, /** @src 1:2834:2843  "isAllowed" */ 0x03)
                    /// @src 1:2814:2859  "owner == manager || isAllowed[owner][manager]"
                    expr := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(sload(/** @src 1:2834:2859  "isAllowed[owner][manager]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ keccak256(/** @src -1:-1:-1 */ 0, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0x40), /** @src 1:2834:2859  "isAllowed[owner][manager]" */ var_manager)), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0xff)
                }
                /// @src 1:2807:2859  "return owner == manager || isAllowed[owner][manager]"
                var := expr
            }
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            function extract_from_storage_value_offsett_uint40(slot_value) -> value
            {
                value := and(shr(208, slot_value), 0xffffffffff)
            }
            function update_storage_value_offsett_uint40_to_uint40(slot, value)
            {
                let _1 := sload(slot)
                sstore(slot, or(and(_1, not(shl(208, 0xffffffffff))), and(shl(208, value), shl(208, 0xffffffffff))))
            }
            /// @src 1:1927:1931  "1e15"
            function update_storage_value_offset_0t_uint64_to_uint64(slot, value)
            {
                sstore(slot, or(and(sload(slot), not(sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1))), and(/** @src 1:1927:1931  "1e15" */ value, sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1))))
            }
            /// @src 1:1927:1931  "1e15"
            function update_storage_value_offsett_uint64_to_t_uint64(slot, value)
            {
                let _1 := sload(slot)
                sstore(slot, or(and(_1, not(sub(shl(128, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), /** @src 1:1927:1931  "1e15" */ shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1)))), /** @src 1:1927:1931  "1e15" */ and(shl(64, value), sub(shl(128, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), /** @src 1:1927:1931  "1e15" */ shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1)))))
            }
            function finalize_allocation(memPtr, size)
            {
                let newFreePtr := add(memPtr, and(add(size, 31), not(31)))
                if or(gt(newFreePtr, /** @src 1:1927:1931  "1e15" */ sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)), lt(newFreePtr, memPtr))
                {
                    mstore(0, shl(224, 0x4e487b71))
                    mstore(4, 0x41)
                    revert(0, 0x24)
                }
                mstore(64, newFreePtr)
            }
            function allocate_and_zero_memory_struct_struct_AssetInfo() -> memPtr
            {
                let memPtr_1 := mload(64)
                finalize_allocation(memPtr_1, 256)
                memPtr := memPtr_1
                /// @src -1:-1:-1
                let _1 := 0
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                mstore(memPtr_1, /** @src -1:-1:-1 */ _1)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                mstore(add(memPtr_1, 32), /** @src -1:-1:-1 */ _1)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                mstore(add(memPtr_1, 64), /** @src -1:-1:-1 */ _1)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                mstore(add(memPtr_1, 96), /** @src -1:-1:-1 */ _1)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                mstore(add(memPtr_1, 128), /** @src -1:-1:-1 */ _1)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                mstore(add(memPtr_1, 160), /** @src -1:-1:-1 */ _1)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                mstore(add(memPtr_1, 192), /** @src -1:-1:-1 */ _1)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                mstore(add(memPtr_1, 224), /** @src -1:-1:-1 */ _1)
            }
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            function abi_decode_uint8_fromMemory(offset) -> value
            {
                value := mload(offset)
                validator_revert_uint8(value)
            }
            function abi_decode_address_fromMemory(offset) -> value
            {
                value := mload(offset)
                validator_revert_address(value)
            }
            function abi_decode_uint64_fromMemory(offset) -> value
            {
                value := mload(offset)
                if iszero(eq(value, and(value, /** @src 1:1927:1931  "1e15" */ sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)))) { revert(0, 0) }
            }
            function abi_decode_uint128_fromMemory(offset) -> value
            {
                value := mload(offset)
                if iszero(eq(value, and(value, /** @src 1:1927:1931  "1e15" */ sub(shl(128, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)))) { revert(0, 0) }
            }
            function revert_forward()
            {
                let pos := mload(64)
                returndatacopy(pos, 0, returndatasize())
                revert(pos, returndatasize())
            }
            /// @ast-id 1659 @src 5:8946:9086  "function getAssetInfo(uint8 i) override public view returns (AssetInfo memory) {..."
            function fun_getAssetInfo(var_i) -> var_mpos
            {
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                pop(allocate_and_zero_memory_struct_struct_AssetInfo())
                /// @src 5:9042:9079  "IAssetList(assetList).getAssetInfo(i)"
                let _1 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                /// @src 5:9042:9079  "IAssetList(assetList).getAssetInfo(i)"
                mstore(_1, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ shl(224, 0xc8c7fe6b))
                mstore(/** @src 5:9042:9079  "IAssetList(assetList).getAssetInfo(i)" */ add(_1, 4), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(var_i, 0xff))
                /// @src 5:9042:9079  "IAssetList(assetList).getAssetInfo(i)"
                let _2 := 256
                let _3 := staticcall(gas(), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:9053:9062  "assetList" */ loadimmutable("1343"), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(shl(160, 1), 1)), /** @src 5:9042:9079  "IAssetList(assetList).getAssetInfo(i)" */ _1, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 36, /** @src 5:9042:9079  "IAssetList(assetList).getAssetInfo(i)" */ _1, _2)
                if iszero(_3) { revert_forward() }
                let expr_1656_mpos := /** @src -1:-1:-1 */ 0
                /// @src 5:9042:9079  "IAssetList(assetList).getAssetInfo(i)"
                if _3
                {
                    let _4 := _2
                    if gt(_2, returndatasize()) { _4 := returndatasize() }
                    finalize_allocation(_1, _4)
                    /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                    if slt(sub(/** @src 5:9042:9079  "IAssetList(assetList).getAssetInfo(i)" */ add(_1, _4), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1), /** @src 5:9042:9079  "IAssetList(assetList).getAssetInfo(i)" */ _2)
                    /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                    {
                        revert(/** @src -1:-1:-1 */ expr_1656_mpos, expr_1656_mpos)
                    }
                    /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                    let memPtr := mload(64)
                    finalize_allocation(memPtr, /** @src 5:9042:9079  "IAssetList(assetList).getAssetInfo(i)" */ _2)
                    /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                    mstore(memPtr, abi_decode_uint8_fromMemory(_1))
                    mstore(add(memPtr, 32), abi_decode_address_fromMemory(add(_1, 32)))
                    mstore(add(memPtr, 64), abi_decode_address_fromMemory(add(_1, 64)))
                    mstore(add(memPtr, 96), abi_decode_uint64_fromMemory(add(_1, 96)))
                    mstore(add(memPtr, 128), abi_decode_uint64_fromMemory(add(_1, 128)))
                    mstore(add(memPtr, 160), abi_decode_uint64_fromMemory(add(_1, 160)))
                    mstore(add(memPtr, 192), abi_decode_uint64_fromMemory(add(_1, 192)))
                    mstore(add(memPtr, 224), abi_decode_uint128_fromMemory(add(_1, 224)))
                    /// @src 5:9042:9079  "IAssetList(assetList).getAssetInfo(i)"
                    expr_1656_mpos := memPtr
                }
                /// @src 5:9035:9079  "return IAssetList(assetList).getAssetInfo(i)"
                var_mpos := expr_1656_mpos
            }
            /// @ast-id 1701 @src 5:9172:9536  "function getAssetInfoByAddress(address asset) override public view returns (AssetInfo memory) {..."
            function fun_getAssetInfoByAddress(var_asset) -> var__mpos
            {
                /// @src 5:9248:9264  "AssetInfo memory"
                var__mpos := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ allocate_and_zero_memory_struct_struct_AssetInfo()
                /// @src 5:9281:9292  "uint8 i = 0"
                let var_i := /** @src 5:9291:9292  "0" */ 0x00
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _1 := 0xff
                /// @src 5:9294:9307  "i < numAssets"
                let _2 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:9298:9307  "numAssets" */ loadimmutable("1337"), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1)
                /// @src 5:9276:9503  "for (uint8 i = 0; i < numAssets; ) {..."
                for { }
                /** @src 5:9294:9307  "i < numAssets" */ lt(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:9294:9307  "i < numAssets" */ var_i, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1), /** @src 5:9294:9307  "i < numAssets" */ _2)
                /// @src 5:9281:9292  "uint8 i = 0"
                { }
                {
                    /// @src 5:9354:9369  "getAssetInfo(i)"
                    let expr_1681_mpos := fun_getAssetInfo(var_i)
                    /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                    let _3 := sub(shl(160, 1), 1)
                    let cleaned := and(mload(/** @src 5:9387:9402  "assetInfo.asset" */ add(expr_1681_mpos, 32)), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _3)
                    /// @src 5:9383:9462  "if (assetInfo.asset == asset) {..."
                    if /** @src 5:9387:9411  "assetInfo.asset == asset" */ eq(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleaned, and(/** @src 5:9387:9411  "assetInfo.asset == asset" */ var_asset, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _3))
                    /// @src 5:9383:9462  "if (assetInfo.asset == asset) {..."
                    {
                        /// @src 5:9431:9447  "return assetInfo"
                        var__mpos := expr_1681_mpos
                        leave
                    }
                    /// @src 5:9487:9490  "i++"
                    var_i := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(add(/** @src 5:9487:9490  "i++" */ var_i, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), _1)
                }
                /// @src 5:9519:9529  "BadAsset()"
                let _4 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                /// @src 5:9519:9529  "BadAsset()"
                mstore(_4, shl(224, 0x36405305))
                revert(_4, 4)
            }
            /// @ast-id 1724 @src 5:9596:9774  "function getNowInternal() virtual internal view returns (uint40) {..."
            function fun_getNowInternal() -> var
            {
                /// @src 5:9671:9727  "if (block.timestamp >= 2**40) revert TimestampTooLarge()"
                if /** @src 5:9675:9699  "block.timestamp >= 2**40" */ iszero(lt(/** @src 5:9675:9690  "block.timestamp" */ timestamp(), /** @src 5:9694:9699  "2**40" */ shl(40, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1)))
                /// @src 5:9671:9727  "if (block.timestamp >= 2**40) revert TimestampTooLarge()"
                {
                    /// @src 5:9708:9727  "TimestampTooLarge()"
                    let _1 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 5:9708:9727  "TimestampTooLarge()"
                    mstore(_1, shl(224, 0x3d32ffdb))
                    revert(_1, 4)
                }
                /// @src 5:9737:9767  "return uint40(block.timestamp)"
                var := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:9675:9690  "block.timestamp" */ timestamp(), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0xffffffffff)
            }
            function write_to_memory_int104(memPtr, value)
            {
                mstore(memPtr, signextend(12, value))
            }
            function write_to_memory_uint64(memPtr, value)
            {
                mstore(memPtr, and(value, /** @src 1:1927:1931  "1e15" */ sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)))
            }
            function write_to_memory_uint16(memPtr, value)
            {
                mstore(memPtr, and(value, 0xffff))
            }
            function write_to_memory_uint8(memPtr, value)
            {
                mstore(memPtr, and(value, 0xff))
            }
            function read_from_storage_reference_type_struct_UserBasic(slot) -> value
            {
                let memPtr := mload(64)
                finalize_allocation(memPtr, 160)
                value := memPtr
                let _1 := sload(slot)
                mstore(memPtr, signextend(12, _1))
                let _2 := /** @src 1:1927:1931  "1e15" */ sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)
                mstore(add(memPtr, 32), and(shr(104, _1), _2))
                mstore(add(memPtr, 64), and(shr(168, _1), _2))
                mstore(add(memPtr, 96), and(shr(232, _1), 0xffff))
                mstore(add(memPtr, 128), shr(248, _1))
            }
            function panic_error_0x11()
            {
                mstore(0, shl(224, 0x4e487b71))
                mstore(4, 0x11)
                revert(0, 0x24)
            }
            function checked_sub_uint40(x, y) -> diff
            {
                let _1 := 0xffffffffff
                let x_1 := and(x, _1)
                let y_1 := and(y, _1)
                if lt(x_1, y_1) { panic_error_0x11() }
                diff := sub(x_1, y_1)
            }
            function convert_uint40_to_uint256(value) -> converted
            {
                converted := and(value, 0xffffffffff)
            }
            function extract_from_storage_value_offsett_uint104(slot_value) -> value
            {
                value := and(slot_value, sub(shl(104, 1), 1))
            }
            function checked_mul_uint256(x, y) -> product
            {
                if and(iszero(iszero(x)), gt(y, div(not(0), x))) { panic_error_0x11() }
                product := mul(x, y)
            }
            function extract_from_storage_value_offsett_uint64(slot_value) -> value
            {
                value := and(shr(128, slot_value), /** @src 1:1927:1931  "1e15" */ sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1))
            }
            function checked_add_uint64(x, y) -> sum
            {
                let _1 := /** @src 1:1927:1931  "1e15" */ sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)
                let x_1 := and(x, _1)
                let y_1 := and(y, _1)
                if gt(x_1, sub(_1, y_1)) { panic_error_0x11() }
                sum := add(x_1, y_1)
            }
            function update_storage_value_offsett_uint64_to_uint64(slot, value)
            {
                let _1 := sload(slot)
                sstore(slot, or(and(_1, not(sub(shl(192, 1), shl(128, 1)))), and(shl(128, value), sub(shl(192, 1), shl(128, 1)))))
            }
            function extract_from_storage_value_offset_13t_uint104(slot_value) -> value
            {
                value := and(shr(104, slot_value), sub(shl(104, 1), 1))
            }
            function extract_from_storage_value_offset_24t_uint64(slot_value) -> value
            { value := shr(192, slot_value) }
            function update_storage_value_offset_24t_uint64_to_uint64(slot, value)
            {
                let _1 := sload(slot)
                sstore(slot, or(and(_1, /** @src 1:1927:1931  "1e15" */ sub(shl(192, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)), and(shl(192, value), not(/** @src 1:1927:1931  "1e15" */ sub(shl(192, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)))))
            }
            /// @ast-id 1859 @src 5:10623:11298  "function accrueInternal() internal {..."
            function fun_accrueInternal()
            {
                /// @src 5:10682:10698  "getNowInternal()"
                let expr := fun_getNowInternal()
                /// @src 5:10727:10758  "uint256(now_ - lastAccrualTime)"
                let expr_1 := convert_uint40_to_uint256(/** @src 5:10735:10757  "now_ - lastAccrualTime" */ checked_sub_uint40(expr, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ extract_from_storage_value_offsett_uint40(sload(/** @src 5:10742:10757  "lastAccrualTime" */ 0x01))))
                /// @src 5:10768:11292  "if (timeElapsed > 0) {..."
                if /** @src 5:10772:10787  "timeElapsed > 0" */ iszero(iszero(expr_1))
                /// @src 5:10768:11292  "if (timeElapsed > 0) {..."
                {
                    /// @src 5:10840:10875  "accruedInterestIndices(timeElapsed)"
                    let expr_1817_component, expr_component := fun_accruedInterestIndices(expr_1)
                    /// @src 5:10786:10787  "0"
                    let _1 := 0x00
                    /// @src 5:10803:10875  "(baseSupplyIndex, baseBorrowIndex) = accruedInterestIndices(timeElapsed)"
                    update_storage_value_offsett_uint64_to_t_uint64(/** @src 5:10786:10787  "0" */ _1, /** @src 5:10803:10875  "(baseSupplyIndex, baseBorrowIndex) = accruedInterestIndices(timeElapsed)" */ expr_component)
                    update_storage_value_offset_0t_uint64_to_uint64(/** @src 5:10786:10787  "0" */ _1, /** @src 5:10803:10875  "(baseSupplyIndex, baseBorrowIndex) = accruedInterestIndices(timeElapsed)" */ expr_1817_component)
                    /// @src 5:10893:10908  "totalSupplyBase"
                    let _2 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ extract_from_storage_value_offsett_uint104(sload(/** @src 5:10742:10757  "lastAccrualTime" */ 0x01))
                    /// @src 5:10893:10929  "totalSupplyBase >= baseMinForRewards"
                    let _3 := /** @src 5:10912:10929  "baseMinForRewards" */ loadimmutable("1321")
                    /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                    let _4 := and(/** @src 5:10893:10929  "totalSupplyBase >= baseMinForRewards" */ _2, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(shl(104, 1), 1))
                    /// @src 5:10889:11061  "if (totalSupplyBase >= baseMinForRewards) {..."
                    if /** @src 5:10893:10929  "totalSupplyBase >= baseMinForRewards" */ iszero(lt(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _4, /** @src 5:10893:10929  "totalSupplyBase >= baseMinForRewards" */ _3))
                    /// @src 5:10889:11061  "if (totalSupplyBase >= baseMinForRewards) {..."
                    {
                        /// @src 5:10949:11046  "trackingSupplyIndex += safe64(divBaseWei(baseTrackingSupplySpeed * timeElapsed, totalSupplyBase))"
                        update_storage_value_offsett_uint64_to_uint64(/** @src 5:10786:10787  "0" */ _1, /** @src 5:10949:11046  "trackingSupplyIndex += safe64(divBaseWei(baseTrackingSupplySpeed * timeElapsed, totalSupplyBase))" */ checked_add_uint64(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ extract_from_storage_value_offsett_uint64(sload(/** @src 5:10786:10787  "0" */ _1)), /** @src 5:10972:11046  "safe64(divBaseWei(baseTrackingSupplySpeed * timeElapsed, totalSupplyBase))" */ fun_safe64(/** @src 5:10979:11045  "divBaseWei(baseTrackingSupplySpeed * timeElapsed, totalSupplyBase)" */ fun_divBaseWei(/** @src 5:10990:11027  "baseTrackingSupplySpeed * timeElapsed" */ checked_mul_uint256(/** @src 5:10990:11013  "baseTrackingSupplySpeed" */ loadimmutable("1313"), /** @src 5:10990:11027  "baseTrackingSupplySpeed * timeElapsed" */ expr_1), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _4))))
                    }
                    /// @src 5:11078:11114  "totalBorrowBase >= baseMinForRewards"
                    let _5 := extract_from_storage_value_offsett_uint104(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ extract_from_storage_value_offset_13t_uint104(sload(/** @src 5:10742:10757  "lastAccrualTime" */ 0x01)))
                    /// @src 5:11074:11246  "if (totalBorrowBase >= baseMinForRewards) {..."
                    if /** @src 5:11078:11114  "totalBorrowBase >= baseMinForRewards" */ iszero(lt(_5, _3))
                    /// @src 5:11074:11246  "if (totalBorrowBase >= baseMinForRewards) {..."
                    {
                        /// @src 5:11134:11231  "trackingBorrowIndex += safe64(divBaseWei(baseTrackingBorrowSpeed * timeElapsed, totalBorrowBase))"
                        update_storage_value_offset_24t_uint64_to_uint64(/** @src 5:10786:10787  "0" */ _1, /** @src 5:11134:11231  "trackingBorrowIndex += safe64(divBaseWei(baseTrackingBorrowSpeed * timeElapsed, totalBorrowBase))" */ checked_add_uint64(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ extract_from_storage_value_offset_24t_uint64(sload(/** @src 5:10786:10787  "0" */ _1)), /** @src 5:11157:11231  "safe64(divBaseWei(baseTrackingBorrowSpeed * timeElapsed, totalBorrowBase))" */ fun_safe64(/** @src 5:11164:11230  "divBaseWei(baseTrackingBorrowSpeed * timeElapsed, totalBorrowBase)" */ fun_divBaseWei(/** @src 5:11175:11212  "baseTrackingBorrowSpeed * timeElapsed" */ checked_mul_uint256(/** @src 5:11175:11198  "baseTrackingBorrowSpeed" */ loadimmutable("1317"), /** @src 5:11175:11212  "baseTrackingBorrowSpeed * timeElapsed" */ expr_1), /** @src 5:11164:11230  "divBaseWei(baseTrackingBorrowSpeed * timeElapsed, totalBorrowBase)" */ _5))))
                    }
                    /// @src 5:11259:11281  "lastAccrualTime = now_"
                    update_storage_value_offsett_uint40_to_uint40(/** @src 5:10742:10757  "lastAccrualTime" */ 0x01, /** @src 5:11259:11281  "lastAccrualTime = now_" */ expr)
                }
            }
            /// @ast-id 960 @src 3:377:523  "function safe64(uint n) internal pure returns (uint64) {..."
            function fun_safe64(var_n) -> var
            {
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _1 := /** @src 1:1927:1931  "1e15" */ sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)
                /// @src 3:442:490  "if (n > type(uint64).max) revert InvalidUInt64()"
                if /** @src 3:446:466  "n > type(uint64).max" */ gt(var_n, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1)
                /// @src 3:442:490  "if (n > type(uint64).max) revert InvalidUInt64()"
                {
                    /// @src 3:475:490  "InvalidUInt64()"
                    let _2 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 3:475:490  "InvalidUInt64()"
                    mstore(_2, shl(225, 0x72a1cb51))
                    revert(_2, 4)
                }
                /// @src 3:500:516  "return uint64(n)"
                var := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 3:507:516  "uint64(n)" */ var_n, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1)
            }
            /// @ast-id 1791 @src 5:9878:10525  "function accruedInterestIndices(uint timeElapsed) internal view returns (uint64, uint64) {..."
            function fun_accruedInterestIndices(var_timeElapsed) -> var, var_1
            {
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _1 := sload(/** @src 5:10003:10018  "baseSupplyIndex" */ 0x00)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _2 := /** @src 1:1927:1931  "1e15" */ sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)
                /// @src 5:9977:10018  "uint64 baseSupplyIndex_ = baseSupplyIndex"
                let var_baseSupplyIndex := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(_1, _2)
                /// @src 5:10028:10069  "uint64 baseBorrowIndex_ = baseBorrowIndex"
                let var_baseBorrowIndex := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(shr(64, _1), _2)
                /// @src 5:10079:10466  "if (timeElapsed > 0) {..."
                if /** @src 5:10083:10098  "timeElapsed > 0" */ iszero(iszero(var_timeElapsed))
                /// @src 5:10079:10466  "if (timeElapsed > 0) {..."
                {
                    /// @src 5:10133:10149  "getUtilization()"
                    let expr := fun_getUtilization()
                    /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                    let cleaned := and(/** @src 5:10181:10207  "getSupplyRate(utilization)" */ fun_getSupplyRate(expr), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _2)
                    let cleaned_1 := and(/** @src 5:10239:10265  "getBorrowRate(utilization)" */ fun_getBorrowRate(expr), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _2)
                    /// @src 1:2135:2139  "1e18"
                    let _3 := 0x0de0b6b3a7640000
                    /// @src 5:10279:10360  "baseSupplyIndex_ += safe64(mulFactor(baseSupplyIndex_, supplyRate * timeElapsed))"
                    var_baseSupplyIndex := checked_add_uint64(var_baseSupplyIndex, /** @src 5:10299:10360  "safe64(mulFactor(baseSupplyIndex_, supplyRate * timeElapsed))" */ fun_safe64(/** @src 1:2135:2139  "1e18" */ div(/** @src 5:21770:21780  "n * factor" */ checked_mul_uint256(var_baseSupplyIndex, /** @src 5:10334:10358  "supplyRate * timeElapsed" */ checked_mul_uint256(cleaned, var_timeElapsed)), /** @src 1:2135:2139  "1e18" */ _3)))
                    /// @src 5:10374:10455  "baseBorrowIndex_ += safe64(mulFactor(baseBorrowIndex_, borrowRate * timeElapsed))"
                    var_baseBorrowIndex := checked_add_uint64(var_baseBorrowIndex, /** @src 5:10394:10455  "safe64(mulFactor(baseBorrowIndex_, borrowRate * timeElapsed))" */ fun_safe64(/** @src 1:2135:2139  "1e18" */ div(/** @src 5:21770:21780  "n * factor" */ checked_mul_uint256(var_baseBorrowIndex, /** @src 5:10429:10453  "borrowRate * timeElapsed" */ checked_mul_uint256(cleaned_1, var_timeElapsed)), /** @src 1:2135:2139  "1e18" */ _3)))
                }
                /// @src 5:10475:10518  "return (baseSupplyIndex_, baseBorrowIndex_)"
                var := var_baseSupplyIndex
                var_1 := var_baseBorrowIndex
            }
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            function checked_add_uint256(x, y) -> sum
            {
                if gt(x, not(y)) { panic_error_0x11() }
                sum := add(x, y)
            }
            function checked_sub_uint256(x, y) -> diff
            {
                if lt(x, y) { panic_error_0x11() }
                diff := sub(x, y)
            }
            /// @ast-id 1926 @src 5:11787:12440  "function getSupplyRate(uint utilization) override public view returns (uint64) {..."
            function fun_getSupplyRate(var_utilization) -> var
            {
                /// @src 5:11895:11905  "supplyKink"
                let _1 := loadimmutable("1269")
                /// @src 5:11876:12434  "if (utilization <= supplyKink) {..."
                switch /** @src 5:11880:11905  "utilization <= supplyKink" */ iszero(gt(var_utilization, _1))
                case /** @src 5:11876:12434  "if (utilization <= supplyKink) {..." */ 0 {
                    /// @src 1:2135:2139  "1e18"
                    let _2 := 0x0de0b6b3a7640000
                    /// @src 5:12252:12344  "supplyPerSecondInterestRateBase + mulFactor(supplyPerSecondInterestRateSlopeLow, supplyKink)"
                    let expr := checked_add_uint256(/** @src 5:12252:12283  "supplyPerSecondInterestRateBase" */ loadimmutable("1281"), /** @src 1:2135:2139  "1e18" */ div(/** @src 5:21770:21780  "n * factor" */ checked_mul_uint256(/** @src 5:12296:12331  "supplyPerSecondInterestRateSlopeLow" */ loadimmutable("1273"), /** @src 5:12286:12344  "mulFactor(supplyPerSecondInterestRateSlopeLow, supplyKink)" */ _1), /** @src 1:2135:2139  "1e18" */ _2))
                    /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                    if lt(var_utilization, _1) { panic_error_0x11() }
                    /// @src 5:12238:12423  "return safe64(supplyPerSecondInterestRateBase + mulFactor(supplyPerSecondInterestRateSlopeLow, supplyKink) + mulFactor(supplyPerSecondInterestRateSlopeHigh, (utilization - supplyKink)))"
                    var := /** @src 5:12245:12423  "safe64(supplyPerSecondInterestRateBase + mulFactor(supplyPerSecondInterestRateSlopeLow, supplyKink) + mulFactor(supplyPerSecondInterestRateSlopeHigh, (utilization - supplyKink)))" */ fun_safe64(/** @src 5:12252:12422  "supplyPerSecondInterestRateBase + mulFactor(supplyPerSecondInterestRateSlopeLow, supplyKink) + mulFactor(supplyPerSecondInterestRateSlopeHigh, (utilization - supplyKink))" */ checked_add_uint256(expr, /** @src 1:2135:2139  "1e18" */ div(/** @src 5:21770:21780  "n * factor" */ checked_mul_uint256(/** @src 5:12357:12393  "supplyPerSecondInterestRateSlopeHigh" */ loadimmutable("1277"), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(var_utilization, _1)), /** @src 1:2135:2139  "1e18" */ _2)))
                    /// @src 5:12238:12423  "return safe64(supplyPerSecondInterestRateBase + mulFactor(supplyPerSecondInterestRateSlopeLow, supplyKink) + mulFactor(supplyPerSecondInterestRateSlopeHigh, (utilization - supplyKink)))"
                    leave
                }
                default /// @src 5:11876:12434  "if (utilization <= supplyKink) {..."
                {
                    /// @src 5:11990:12098  "return safe64(supplyPerSecondInterestRateBase + mulFactor(supplyPerSecondInterestRateSlopeLow, utilization))"
                    var := /** @src 5:11997:12098  "safe64(supplyPerSecondInterestRateBase + mulFactor(supplyPerSecondInterestRateSlopeLow, utilization))" */ fun_safe64(/** @src 5:12004:12097  "supplyPerSecondInterestRateBase + mulFactor(supplyPerSecondInterestRateSlopeLow, utilization)" */ checked_add_uint256(/** @src 5:12004:12035  "supplyPerSecondInterestRateBase" */ loadimmutable("1281"), /** @src 1:2135:2139  "1e18" */ div(/** @src 5:21770:21780  "n * factor" */ checked_mul_uint256(/** @src 5:12048:12083  "supplyPerSecondInterestRateSlopeLow" */ loadimmutable("1273"), /** @src 5:12038:12097  "mulFactor(supplyPerSecondInterestRateSlopeLow, utilization)" */ var_utilization), /** @src 1:2135:2139  "1e18" */ 0x0de0b6b3a7640000)))
                    /// @src 5:11990:12098  "return safe64(supplyPerSecondInterestRateBase + mulFactor(supplyPerSecondInterestRateSlopeLow, utilization))"
                    leave
                }
            }
            /// @ast-id 1968 @src 5:12641:13294  "function getBorrowRate(uint utilization) override public view returns (uint64) {..."
            function fun_getBorrowRate(var_utilization) -> var
            {
                /// @src 5:12749:12759  "borrowKink"
                let _1 := loadimmutable("1285")
                /// @src 5:12730:13288  "if (utilization <= borrowKink) {..."
                switch /** @src 5:12734:12759  "utilization <= borrowKink" */ iszero(gt(var_utilization, _1))
                case /** @src 5:12730:13288  "if (utilization <= borrowKink) {..." */ 0 {
                    /// @src 1:2135:2139  "1e18"
                    let _2 := 0x0de0b6b3a7640000
                    /// @src 5:13106:13198  "borrowPerSecondInterestRateBase + mulFactor(borrowPerSecondInterestRateSlopeLow, borrowKink)"
                    let expr := checked_add_uint256(/** @src 5:13106:13137  "borrowPerSecondInterestRateBase" */ loadimmutable("1297"), /** @src 1:2135:2139  "1e18" */ div(/** @src 5:21770:21780  "n * factor" */ checked_mul_uint256(/** @src 5:13150:13185  "borrowPerSecondInterestRateSlopeLow" */ loadimmutable("1289"), /** @src 5:13140:13198  "mulFactor(borrowPerSecondInterestRateSlopeLow, borrowKink)" */ _1), /** @src 1:2135:2139  "1e18" */ _2))
                    /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                    if lt(var_utilization, _1) { panic_error_0x11() }
                    /// @src 5:13092:13277  "return safe64(borrowPerSecondInterestRateBase + mulFactor(borrowPerSecondInterestRateSlopeLow, borrowKink) + mulFactor(borrowPerSecondInterestRateSlopeHigh, (utilization - borrowKink)))"
                    var := /** @src 5:13099:13277  "safe64(borrowPerSecondInterestRateBase + mulFactor(borrowPerSecondInterestRateSlopeLow, borrowKink) + mulFactor(borrowPerSecondInterestRateSlopeHigh, (utilization - borrowKink)))" */ fun_safe64(/** @src 5:13106:13276  "borrowPerSecondInterestRateBase + mulFactor(borrowPerSecondInterestRateSlopeLow, borrowKink) + mulFactor(borrowPerSecondInterestRateSlopeHigh, (utilization - borrowKink))" */ checked_add_uint256(expr, /** @src 1:2135:2139  "1e18" */ div(/** @src 5:21770:21780  "n * factor" */ checked_mul_uint256(/** @src 5:13211:13247  "borrowPerSecondInterestRateSlopeHigh" */ loadimmutable("1293"), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(var_utilization, _1)), /** @src 1:2135:2139  "1e18" */ _2)))
                    /// @src 5:13092:13277  "return safe64(borrowPerSecondInterestRateBase + mulFactor(borrowPerSecondInterestRateSlopeLow, borrowKink) + mulFactor(borrowPerSecondInterestRateSlopeHigh, (utilization - borrowKink)))"
                    leave
                }
                default /// @src 5:12730:13288  "if (utilization <= borrowKink) {..."
                {
                    /// @src 5:12844:12952  "return safe64(borrowPerSecondInterestRateBase + mulFactor(borrowPerSecondInterestRateSlopeLow, utilization))"
                    var := /** @src 5:12851:12952  "safe64(borrowPerSecondInterestRateBase + mulFactor(borrowPerSecondInterestRateSlopeLow, utilization))" */ fun_safe64(/** @src 5:12858:12951  "borrowPerSecondInterestRateBase + mulFactor(borrowPerSecondInterestRateSlopeLow, utilization)" */ checked_add_uint256(/** @src 5:12858:12889  "borrowPerSecondInterestRateBase" */ loadimmutable("1297"), /** @src 1:2135:2139  "1e18" */ div(/** @src 5:21770:21780  "n * factor" */ checked_mul_uint256(/** @src 5:12902:12937  "borrowPerSecondInterestRateSlopeLow" */ loadimmutable("1289"), /** @src 5:12892:12951  "mulFactor(borrowPerSecondInterestRateSlopeLow, utilization)" */ var_utilization), /** @src 1:2135:2139  "1e18" */ 0x0de0b6b3a7640000)))
                    /// @src 5:12844:12952  "return safe64(borrowPerSecondInterestRateBase + mulFactor(borrowPerSecondInterestRateSlopeLow, utilization))"
                    leave
                }
            }
            /// @src 1:2135:2139  "1e18"
            function panic_error_0x12()
            {
                mstore(0, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ shl(224, 0x4e487b71))
                /// @src 1:2135:2139  "1e18"
                mstore(4, 0x12)
                revert(0, 0x24)
            }
            function checked_div_uint256(x, y) -> r
            {
                if iszero(y) { panic_error_0x12() }
                r := div(x, y)
            }
            /// @ast-id 2004 @src 5:13419:13797  "function getUtilization() override public view returns (uint) {..."
            function fun_getUtilization() -> var
            {
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _1 := sload(/** @src 5:13530:13545  "baseSupplyIndex" */ 0x00)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _2 := /** @src 1:1927:1931  "1e15" */ sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)
                let _3 := sload(/** @src 5:13547:13562  "totalSupplyBase" */ 0x01)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _4 := sub(shl(104, 1), 1)
                /// @src 5:13511:13563  "presentValueSupply(baseSupplyIndex, totalSupplyBase)"
                let expr := fun_presentValueSupply(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(_1, _2), and(_3, _4))
                /// @src 5:13593:13645  "presentValueBorrow(baseBorrowIndex, totalBorrowBase)"
                let expr_1 := fun_presentValueSupply(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(shr(64, _1), _2), and(shr(104, _3), _4))
                /// @src 5:13655:13791  "if (totalSupply_ == 0) {..."
                switch /** @src 5:13659:13676  "totalSupply_ == 0" */ iszero(expr)
                case /** @src 5:13655:13791  "if (totalSupply_ == 0) {..." */ 0 {
                    /// @src 1:2135:2139  "1e18"
                    let _5 := 0x0de0b6b3a7640000
                    /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                    if and(iszero(iszero(expr_1)), gt(/** @src 1:2135:2139  "1e18" */ _5, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ div(not(0), expr_1))) { panic_error_0x11() }
                    /// @src 5:13731:13780  "return totalBorrow_ * FACTOR_SCALE / totalSupply_"
                    var := /** @src 1:2135:2139  "1e18" */ div(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mul(expr_1, /** @src 1:2135:2139  "1e18" */ _5), expr)
                    /// @src 5:13731:13780  "return totalBorrow_ * FACTOR_SCALE / totalSupply_"
                    leave
                }
                default /// @src 5:13655:13791  "if (totalSupply_ == 0) {..."
                {
                    /// @src 5:13692:13700  "return 0"
                    var := /** @src 5:13530:13545  "baseSupplyIndex" */ 0x00
                    /// @src 5:13692:13700  "return 0"
                    leave
                }
            }
            /// @ast-id 247 @src 1:3419:3615  "function presentValueSupply(uint64 baseSupplyIndex_, uint104 principalValue_) internal pure returns (uint256) {..."
            function fun_presentValueSupply(var_baseSupplyIndex_, var_principalValue) -> var
            {
                /// @src 1:3539:3608  "return uint256(principalValue_) * baseSupplyIndex_ / BASE_INDEX_SCALE"
                var := /** @src 1:2135:2139  "1e18" */ div(/** @src 1:3546:3589  "uint256(principalValue_) * baseSupplyIndex_" */ checked_mul_uint256(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 1:3546:3570  "uint256(principalValue_)" */ var_principalValue, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(shl(104, 1), 1)), and(/** @src 1:3546:3589  "uint256(principalValue_) * baseSupplyIndex_" */ var_baseSupplyIndex_, /** @src 1:1927:1931  "1e15" */ sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1))), /** @src 1:1927:1931  "1e15" */ 0x038d7ea4c68000)
            }
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            function abi_decode_uint80_fromMemory(offset) -> value
            {
                value := mload(offset)
                if iszero(eq(value, and(value, sub(shl(80, 1), 1)))) { revert(0, 0) }
            }
            /// @ast-id 2034 @src 5:13970:14198  "function getPrice(address priceFeed) override public view returns (uint256) {..."
            function fun_getPrice(var_priceFeed) -> var
            {
                /// @src 5:14078:14117  "IPriceFeed(priceFeed).latestRoundData()"
                let _1 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                /// @src 5:14078:14117  "IPriceFeed(priceFeed).latestRoundData()"
                mstore(_1, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ shl(226, 0x3fabe5a3))
                /// @src 5:14078:14117  "IPriceFeed(priceFeed).latestRoundData()"
                let _2 := staticcall(gas(), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:14078:14099  "IPriceFeed(priceFeed)" */ var_priceFeed, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(shl(160, 1), 1)), /** @src 5:14078:14117  "IPriceFeed(priceFeed).latestRoundData()" */ _1, 4, _1, 160)
                if iszero(_2) { revert_forward() }
                let expr_2019_component := 0
                if _2
                {
                    let _3 := 160
                    if gt(_3, returndatasize()) { _3 := returndatasize() }
                    finalize_allocation(_1, _3)
                    /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                    if slt(sub(/** @src 5:14078:14117  "IPriceFeed(priceFeed).latestRoundData()" */ add(_1, _3), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1), /** @src 5:14078:14117  "IPriceFeed(priceFeed).latestRoundData()" */ 160)
                    /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                    {
                        revert(/** @src 5:14078:14117  "IPriceFeed(priceFeed).latestRoundData()" */ expr_2019_component, expr_2019_component)
                    }
                    /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                    pop(abi_decode_uint80_fromMemory(_1))
                    let value := mload(add(_1, 32))
                    pop(abi_decode_uint80_fromMemory(add(_1, 128)))
                    /// @src 5:14078:14117  "IPriceFeed(priceFeed).latestRoundData()"
                    expr_2019_component := value
                }
                /// @src 5:14127:14160  "if (price <= 0) revert BadPrice()"
                if /** @src 5:14131:14141  "price <= 0" */ iszero(sgt(expr_2019_component, /** @src 5:14078:14117  "IPriceFeed(priceFeed).latestRoundData()" */ 0))
                /// @src 5:14127:14160  "if (price <= 0) revert BadPrice()"
                {
                    /// @src 5:14150:14160  "BadPrice()"
                    let _4 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 5:14150:14160  "BadPrice()"
                    mstore(_4, shl(224, 0xfd1ee349))
                    revert(_4, /** @src 5:14078:14117  "IPriceFeed(priceFeed).latestRoundData()" */ 4)
                }
                /// @src 5:14170:14191  "return uint256(price)"
                var := expr_2019_component
            }
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            function abi_decode_uint256_fromMemory(headStart, dataEnd) -> value0
            {
                if slt(sub(dataEnd, headStart), 32) { revert(0, 0) }
                value0 := mload(headStart)
            }
            /// @ast-id 2059 @src 5:14444:14642  "function getCollateralReserves(address asset) override public view returns (uint) {..."
            function fun_getCollateralReserves(var_asset) -> var_
            {
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _1 := and(/** @src 5:14543:14567  "IERC20NonStandard(asset)" */ var_asset, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(shl(160, 1), 1))
                /// @src 5:14543:14592  "IERC20NonStandard(asset).balanceOf(address(this))"
                let _2 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                /// @src 5:14543:14592  "IERC20NonStandard(asset).balanceOf(address(this))"
                mstore(_2, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ shl(224, 0x70a08231))
                mstore(/** @src 5:14543:14592  "IERC20NonStandard(asset).balanceOf(address(this))" */ add(_2, 4), /** @src 5:14586:14590  "this" */ address())
                /// @src 5:14543:14592  "IERC20NonStandard(asset).balanceOf(address(this))"
                let _3 := staticcall(gas(), _1, _2, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 36, /** @src 5:14543:14592  "IERC20NonStandard(asset).balanceOf(address(this))" */ _2, 32)
                if iszero(_3) { revert_forward() }
                let expr := /** @src -1:-1:-1 */ 0
                /// @src 5:14543:14592  "IERC20NonStandard(asset).balanceOf(address(this))"
                if _3
                {
                    let _4 := 32
                    if gt(_4, returndatasize()) { _4 := returndatasize() }
                    finalize_allocation(_2, _4)
                    expr := abi_decode_uint256_fromMemory(_2, add(_2, _4))
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                mstore(/** @src -1:-1:-1 */ 0, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1)
                mstore(/** @src 5:14543:14592  "IERC20NonStandard(asset).balanceOf(address(this))" */ 32, /** @src 5:14595:14611  "totalsCollateral" */ 0x02)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let value := and(sload(keccak256(/** @src -1:-1:-1 */ 0, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 64)), /** @src 1:1927:1931  "1e15" */ sub(shl(128, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1))
                if lt(expr, value) { panic_error_0x11() }
                /// @src 5:14536:14635  "return IERC20NonStandard(asset).balanceOf(address(this)) - totalsCollateral[asset].totalSupplyAsset"
                var_ := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(expr, value)
            }
            function checked_sub_int256(x, y) -> diff
            {
                let _1 := slt(y, 0)
                if and(iszero(_1), slt(x, add(shl(255, 1), y))) { panic_error_0x11() }
                if and(_1, sgt(x, add(sub(shl(255, 1), 1), y))) { panic_error_0x11() }
                diff := sub(x, y)
            }
            function checked_add_int256(x, y) -> sum
            {
                let _1 := slt(x, 0)
                if and(iszero(_1), sgt(y, sub(sub(shl(255, 1), 1), x))) { panic_error_0x11() }
                if and(_1, slt(y, sub(shl(255, 1), x))) { panic_error_0x11() }
                sum := add(x, y)
            }
            /// @ast-id 2116 @src 5:14740:15257  "function getReserves() override public view returns (int) {..."
            function fun_getReserves() -> var
            {
                /// @src 5:14884:14900  "getNowInternal()"
                let expr := fun_getNowInternal()
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _1 := sload(/** @src 5:14903:14918  "lastAccrualTime" */ 0x01)
                /// @src 5:14861:14919  "accruedInterestIndices(getNowInternal() - lastAccrualTime)"
                let expr_2075_component, expr_2075_component_1 := fun_accruedInterestIndices(convert_uint40_to_uint256(/** @src 5:14884:14918  "getNowInternal() - lastAccrualTime" */ checked_sub_uint40(expr, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(shr(208, _1), 0xffffffffff))))
                /// @src 5:14944:14997  "IERC20NonStandard(baseToken).balanceOf(address(this))"
                let _2 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                /// @src 5:14944:14997  "IERC20NonStandard(baseToken).balanceOf(address(this))"
                mstore(_2, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ shl(224, 0x70a08231))
                /// @src 5:14944:14997  "IERC20NonStandard(baseToken).balanceOf(address(this))"
                let _3 := staticcall(gas(), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:14962:14971  "baseToken" */ loadimmutable("1257"), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(shl(160, 1), 1)), /** @src 5:14944:14997  "IERC20NonStandard(baseToken).balanceOf(address(this))" */ _2, sub(abi_encode_address(add(_2, 4), /** @src 5:14991:14995  "this" */ address()), /** @src 5:14944:14997  "IERC20NonStandard(baseToken).balanceOf(address(this))" */ _2), _2, 32)
                if iszero(_3) { revert_forward() }
                let expr_1 := /** @src -1:-1:-1 */ 0
                /// @src 5:14944:14997  "IERC20NonStandard(baseToken).balanceOf(address(this))"
                if _3
                {
                    let _4 := 32
                    if gt(_4, returndatasize()) { _4 := returndatasize() }
                    finalize_allocation(_2, _4)
                    expr_1 := abi_decode_uint256_fromMemory(_2, add(_2, _4))
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _5 := sub(shl(104, 1), 1)
                /// @src 5:15027:15080  "presentValueSupply(baseSupplyIndex_, totalSupplyBase)"
                let expr_2 := fun_presentValueSupply(expr_2075_component, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(_1, _5))
                /// @src 5:15110:15163  "presentValueBorrow(baseBorrowIndex_, totalBorrowBase)"
                let expr_3 := fun_presentValueSupply(expr_2075_component_1, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(shr(104, _1), _5))
                /// @src 5:15180:15198  "signed256(balance)"
                let expr_4 := fun_signed256(expr_1)
                /// @src 5:15180:15224  "signed256(balance) - signed256(totalSupply_)"
                let expr_5 := checked_sub_int256(expr_4, /** @src 5:15201:15224  "signed256(totalSupply_)" */ fun_signed256(expr_2))
                /// @src 5:15173:15250  "return signed256(balance) - signed256(totalSupply_) + signed256(totalBorrow_)"
                var := /** @src 5:15180:15250  "signed256(balance) - signed256(totalSupply_) + signed256(totalBorrow_)" */ checked_add_int256(expr_5, /** @src 5:15227:15250  "signed256(totalBorrow_)" */ fun_signed256(expr_3))
            }
            /// @ast-id 1062 @src 3:1010:1171  "function signed256(uint256 n) internal pure returns (int256) {..."
            function fun_signed256(var_n) -> var
            {
                /// @src 3:1081:1138  "if (n > uint256(type(int256).max)) revert InvalidInt256()"
                if /** @src 3:1085:1114  "n > uint256(type(int256).max)" */ gt(var_n, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(shl(255, 1), 1))
                /// @src 3:1081:1138  "if (n > uint256(type(int256).max)) revert InvalidInt256()"
                {
                    /// @src 3:1123:1138  "InvalidInt256()"
                    let _1 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 3:1123:1138  "InvalidInt256()"
                    mstore(_1, shl(224, 0xe7e828ad))
                    revert(_1, 4)
                }
                /// @src 3:1148:1164  "return int256(n)"
                var := var_n
            }
            /// @ast-id 2235 @src 5:15474:16652  "function isBorrowCollateralized(address account) override public view returns (bool) {..."
            function fun_isBorrowCollateralized(var_account) -> var
            {
                /// @src 5:15588:15616  "userBasic[account].principal"
                let _1 := read_from_storage_split_offset_int104(/** @src 5:15588:15606  "userBasic[account]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:15588:15597  "userBasic" */ 0x05, /** @src 5:15588:15606  "userBasic[account]" */ var_account))
                /// @src 5:15588:15616  "userBasic[account].principal"
                let _2 := 0
                /// @src 5:15627:15683  "if (principal >= 0) {..."
                if /** @src 5:15631:15645  "principal >= 0" */ iszero(slt(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ signextend(12, /** @src 5:15631:15645  "principal >= 0" */ _1), /** @src 5:15588:15616  "userBasic[account].principal" */ _2))
                /// @src 5:15627:15683  "if (principal >= 0) {..."
                {
                    /// @src 5:15661:15672  "return true"
                    var := /** @src 5:15668:15672  "true" */ 0x01
                    /// @src 5:15661:15672  "return true"
                    leave
                }
                /// @src 5:15711:15738  "userBasic[account].assetsIn"
                let _3 := read_from_storage_split_offset_uint16(/** @src 5:15711:15729  "userBasic[account]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:15588:15597  "userBasic" */ 0x05, /** @src 5:15711:15729  "userBasic[account]" */ var_account))
                /// @src 5:15766:15794  "userBasic[account]._reserved"
                let _4 := read_from_storage_split_offset_uint8(/** @src 5:15766:15784  "userBasic[account]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:15588:15597  "userBasic" */ 0x05, /** @src 5:15766:15784  "userBasic[account]" */ var_account))
                /// @src 5:15848:15871  "presentValue(principal)"
                let expr := fun_presentValue(_1)
                /// @src 5:15885:15913  "getPrice(baseTokenPriceFeed)"
                let expr_1 := fun_getPrice(/** @src 5:15894:15912  "baseTokenPriceFeed" */ loadimmutable("1261"))
                /// @src 5:15804:15954  "int liquidity = signedMulPrice(..."
                let var_liquidity := /** @src 5:15820:15954  "signedMulPrice(..." */ fun_signedMulPrice(expr, expr_1, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:15934:15943  "baseScale" */ loadimmutable("1305"), /** @src 1:1927:1931  "1e15" */ sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)))
                /// @src 5:15970:15981  "uint8 i = 0"
                let var_i := /** @src 5:15588:15616  "userBasic[account].principal" */ _2
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _5 := 0xff
                /// @src 5:15983:15996  "i < numAssets"
                let _6 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:15987:15996  "numAssets" */ loadimmutable("1337"), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _5)
                /// @src 5:15965:16614  "for (uint8 i = 0; i < numAssets; ) {..."
                for { }
                /** @src 5:15983:15996  "i < numAssets" */ lt(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:15983:15996  "i < numAssets" */ var_i, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _5), /** @src 5:15983:15996  "i < numAssets" */ _6)
                /// @src 5:15970:15981  "uint8 i = 0"
                { }
                {
                    /// @src 5:16014:16573  "if (isInAsset(assetsIn, i, _reserved)) {..."
                    if /** @src 5:16018:16051  "isInAsset(assetsIn, i, _reserved)" */ fun_isInAsset(_3, var_i, _4)
                    /// @src 5:16014:16573  "if (isInAsset(assetsIn, i, _reserved)) {..."
                    {
                        /// @src 5:16071:16143  "if (liquidity >= 0) {..."
                        if /** @src 5:16075:16089  "liquidity >= 0" */ iszero(slt(var_liquidity, /** @src 5:15588:15616  "userBasic[account].principal" */ _2))
                        /// @src 5:16071:16143  "if (liquidity >= 0) {..."
                        {
                            /// @src 5:16113:16124  "return true"
                            var := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1
                            /// @src 5:16113:16124  "return true"
                            leave
                        }
                        /// @src 5:16186:16201  "getAssetInfo(i)"
                        let expr_2192_mpos := fun_getAssetInfo(var_i)
                        /// @src 5:16266:16289  "userCollateral[account]"
                        let _7 := mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:16266:16280  "userCollateral" */ 0x06, /** @src 5:16266:16289  "userCollateral[account]" */ var_account)
                        /// @src 5:16266:16310  "userCollateral[account][asset.asset].balance"
                        let _8 := read_from_storage_split_offset_uint128(/** @src 5:16266:16302  "userCollateral[account][asset.asset]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(_7, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_address(mload(/** @src 5:16290:16301  "asset.asset" */ add(expr_2192_mpos, 32)))))
                        /// @src 5:16332:16357  "getPrice(asset.priceFeed)"
                        let expr_2 := fun_getPrice(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_address(mload(/** @src 5:16341:16356  "asset.priceFeed" */ add(expr_2192_mpos, 64))))
                        /// @src 5:16236:16408  "mulPrice(..."
                        let expr_3 := fun_mulPrice(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:16236:16408  "mulPrice(..." */ _8, /** @src 1:1927:1931  "1e15" */ sub(shl(128, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)), /** @src 5:16236:16408  "mulPrice(..." */ expr_2, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_uint64(mload(/** @src 5:16379:16390  "asset.scale" */ add(expr_2192_mpos, 96))))
                        /// @src 5:16426:16558  "liquidity += signed256(mulFactor(..."
                        var_liquidity := checked_add_int256(var_liquidity, /** @src 5:16439:16558  "signed256(mulFactor(..." */ fun_signed256(/** @src 5:16449:16557  "mulFactor(..." */ fun_mulFactor(expr_3, cleanup_uint64(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_uint64(mload(/** @src 5:16511:16539  "asset.borrowCollateralFactor" */ add(expr_2192_mpos, 128)))))))
                    }
                    /// @src 5:16598:16601  "i++"
                    var_i := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(add(/** @src 5:16598:16601  "i++" */ var_i, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), _5)
                }
                /// @src 5:16624:16645  "return liquidity >= 0"
                var := /** @src 5:16631:16645  "liquidity >= 0" */ iszero(slt(var_liquidity, /** @src 5:15588:15616  "userBasic[account].principal" */ _2))
            }
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            function negate_int104(value) -> ret
            {
                let value_1 := signextend(12, value)
                if eq(value_1, not(sub(shl(103, 1), 1))) { panic_error_0x11() }
                ret := sub(0, value_1)
            }
            function convert_int104_to_uint104(value) -> converted
            {
                converted := and(sub(shl(104, 1), 1), value)
            }
            function negate_int256(value) -> ret
            {
                if eq(value, shl(255, 1)) { panic_error_0x11() }
                ret := sub(0, value)
            }
            /// @ast-id 227 @src 1:2991:3326  "function presentValue(int104 principalValue_) internal view returns (int256) {..."
            function fun_presentValue(var_principalValue) -> var
            {
                /// @src 1:3078:3320  "if (principalValue_ >= 0) {..."
                switch /** @src 1:3082:3102  "principalValue_ >= 0" */ iszero(slt(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ signextend(12, /** @src 1:3082:3102  "principalValue_ >= 0" */ var_principalValue), /** @src 1:3101:3102  "0" */ 0x00))
                case /** @src 1:3078:3320  "if (principalValue_ >= 0) {..." */ 0 {
                    /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                    let value := and(shr(64, sload(/** @src 1:3101:3102  "0" */ 0x00)), /** @src 1:1927:1931  "1e15" */ sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1))
                    /// @src 1:3228:3309  "return -signed256(presentValueBorrow(baseBorrowIndex, uint104(-principalValue_)))"
                    var := /** @src 1:3235:3309  "-signed256(presentValueBorrow(baseBorrowIndex, uint104(-principalValue_)))" */ negate_int256(/** @src 1:3236:3309  "signed256(presentValueBorrow(baseBorrowIndex, uint104(-principalValue_)))" */ fun_signed256(/** @src 1:3246:3308  "presentValueBorrow(baseBorrowIndex, uint104(-principalValue_))" */ fun_presentValueSupply(value, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(sub(shl(104, 1), 1), /** @src 1:3290:3306  "-principalValue_" */ negate_int104(var_principalValue)))))
                    /// @src 1:3228:3309  "return -signed256(presentValueBorrow(baseBorrowIndex, uint104(-principalValue_)))"
                    leave
                }
                default /// @src 1:3078:3320  "if (principalValue_ >= 0) {..."
                {
                    /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                    let cleaned := and(sload(/** @src 1:3101:3102  "0" */ 0x00), /** @src 1:1927:1931  "1e15" */ sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1))
                    /// @src 1:3118:3197  "return signed256(presentValueSupply(baseSupplyIndex, uint104(principalValue_)))"
                    var := /** @src 1:3125:3197  "signed256(presentValueSupply(baseSupplyIndex, uint104(principalValue_)))" */ fun_signed256(/** @src 1:3135:3196  "presentValueSupply(baseSupplyIndex, uint104(principalValue_))" */ fun_presentValueSupply(cleaned, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(sub(shl(104, 1), 1), /** @src 1:3082:3102  "principalValue_ >= 0" */ var_principalValue)))
                    /// @src 1:3118:3197  "return signed256(presentValueSupply(baseSupplyIndex, uint104(principalValue_)))"
                    leave
                }
            }
            /// @ast-id 2354 @src 5:16891:18065  "function isLiquidatable(address account) override public view returns (bool) {..."
            function fun_isLiquidatable(var_account) -> var
            {
                /// @src 5:16997:17025  "userBasic[account].principal"
                let _1 := read_from_storage_split_offset_int104(/** @src 5:16997:17015  "userBasic[account]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:16997:17006  "userBasic" */ 0x05, /** @src 5:16997:17015  "userBasic[account]" */ var_account))
                /// @src 5:16997:17025  "userBasic[account].principal"
                let _2 := 0
                /// @src 5:17036:17093  "if (principal >= 0) {..."
                if /** @src 5:17040:17054  "principal >= 0" */ iszero(slt(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ signextend(12, /** @src 5:17040:17054  "principal >= 0" */ _1), /** @src 5:16997:17025  "userBasic[account].principal" */ _2))
                /// @src 5:17036:17093  "if (principal >= 0) {..."
                {
                    /// @src 5:17070:17082  "return false"
                    var := /** @src 5:16997:17025  "userBasic[account].principal" */ _2
                    /// @src 5:17070:17082  "return false"
                    leave
                }
                /// @src 5:17121:17148  "userBasic[account].assetsIn"
                let _3 := read_from_storage_split_offset_uint16(/** @src 5:17121:17139  "userBasic[account]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:16997:17006  "userBasic" */ 0x05, /** @src 5:17121:17139  "userBasic[account]" */ var_account))
                /// @src 5:17176:17204  "userBasic[account]._reserved"
                let _4 := read_from_storage_split_offset_uint8(/** @src 5:17176:17194  "userBasic[account]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:16997:17006  "userBasic" */ 0x05, /** @src 5:17176:17194  "userBasic[account]" */ var_account))
                /// @src 5:17258:17281  "presentValue(principal)"
                let expr := fun_presentValue(_1)
                /// @src 5:17295:17323  "getPrice(baseTokenPriceFeed)"
                let expr_1 := fun_getPrice(/** @src 5:17304:17322  "baseTokenPriceFeed" */ loadimmutable("1261"))
                /// @src 5:17214:17364  "int liquidity = signedMulPrice(..."
                let var_liquidity := /** @src 5:17230:17364  "signedMulPrice(..." */ fun_signedMulPrice(expr, expr_1, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:17344:17353  "baseScale" */ loadimmutable("1305"), /** @src 1:1927:1931  "1e15" */ sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)))
                /// @src 5:17380:17391  "uint8 i = 0"
                let var_i := /** @src 5:16997:17025  "userBasic[account].principal" */ _2
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _5 := 0xff
                /// @src 5:17393:17406  "i < numAssets"
                let _6 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:17397:17406  "numAssets" */ loadimmutable("1337"), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _5)
                /// @src 5:17375:18028  "for (uint8 i = 0; i < numAssets; ) {..."
                for { }
                /** @src 5:17393:17406  "i < numAssets" */ lt(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:17393:17406  "i < numAssets" */ var_i, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _5), /** @src 5:17393:17406  "i < numAssets" */ _6)
                /// @src 5:17380:17391  "uint8 i = 0"
                { }
                {
                    /// @src 5:17424:17987  "if (isInAsset(assetsIn, i, _reserved)) {..."
                    if /** @src 5:17428:17461  "isInAsset(assetsIn, i, _reserved)" */ fun_isInAsset(_3, var_i, _4)
                    /// @src 5:17424:17987  "if (isInAsset(assetsIn, i, _reserved)) {..."
                    {
                        /// @src 5:17481:17554  "if (liquidity >= 0) {..."
                        if /** @src 5:17485:17499  "liquidity >= 0" */ iszero(slt(var_liquidity, /** @src 5:16997:17025  "userBasic[account].principal" */ _2))
                        /// @src 5:17481:17554  "if (liquidity >= 0) {..."
                        {
                            /// @src 5:17523:17535  "return false"
                            var := /** @src 5:16997:17025  "userBasic[account].principal" */ _2
                            /// @src 5:17523:17535  "return false"
                            leave
                        }
                        /// @src 5:17597:17612  "getAssetInfo(i)"
                        let expr_2311_mpos := fun_getAssetInfo(var_i)
                        /// @src 5:17677:17700  "userCollateral[account]"
                        let _7 := mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:17677:17691  "userCollateral" */ 0x06, /** @src 5:17677:17700  "userCollateral[account]" */ var_account)
                        /// @src 5:17677:17721  "userCollateral[account][asset.asset].balance"
                        let _8 := read_from_storage_split_offset_uint128(/** @src 5:17677:17713  "userCollateral[account][asset.asset]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(_7, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_address(mload(/** @src 5:17701:17712  "asset.asset" */ add(expr_2311_mpos, 32)))))
                        /// @src 5:17743:17768  "getPrice(asset.priceFeed)"
                        let expr_2 := fun_getPrice(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_address(mload(/** @src 5:17752:17767  "asset.priceFeed" */ add(expr_2311_mpos, 64))))
                        /// @src 5:17647:17819  "mulPrice(..."
                        let expr_3 := fun_mulPrice(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:17647:17819  "mulPrice(..." */ _8, /** @src 1:1927:1931  "1e15" */ sub(shl(128, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)), /** @src 5:17647:17819  "mulPrice(..." */ expr_2, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_uint64(mload(/** @src 5:17790:17801  "asset.scale" */ add(expr_2311_mpos, 96))))
                        /// @src 5:17837:17972  "liquidity += signed256(mulFactor(..."
                        var_liquidity := checked_add_int256(var_liquidity, /** @src 5:17850:17972  "signed256(mulFactor(..." */ fun_signed256(/** @src 5:17860:17971  "mulFactor(..." */ fun_mulFactor(expr_3, cleanup_uint64(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_uint64(mload(/** @src 5:17922:17953  "asset.liquidateCollateralFactor" */ add(expr_2311_mpos, 160)))))))
                    }
                    /// @src 5:18012:18015  "i++"
                    var_i := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(add(/** @src 5:18012:18015  "i++" */ var_i, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), _5)
                }
                /// @src 5:18038:18058  "return liquidity < 0"
                var := /** @src 5:18045:18058  "liquidity < 0" */ slt(var_liquidity, /** @src 5:16997:17025  "userBasic[account].principal" */ _2)
            }
            /// @src 1:1247:1248  "0"
            function shift_left_uint8_uint8(value, bits) -> result
            {
                result := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 1:1247:1248  "0" */ shl(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 1:1247:1248  "0" */ bits, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0xff), and(/** @src 1:1247:1248  "0" */ value, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0xff)), 0xff)
            }
            /// @src 1:1460:1461  "4"
            function update_storage_value_offsett_uint8_to_uint8(slot, value)
            {
                let _1 := sload(slot)
                sstore(slot, or(and(_1, sub(shl(248, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)), /** @src 1:1460:1461  "4" */ and(shl(248, value), shl(248, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 255))))
            }
            /// @src 1:1460:1461  "4"
            function abi_encode_bool_bool_bool_bool_bool(headStart, value0, value1, value2, value3, value4) -> tail
            {
                tail := add(headStart, 160)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                mstore(headStart, iszero(iszero(value0)))
                mstore(/** @src 1:1460:1461  "4" */ add(headStart, 32), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ iszero(iszero(value1)))
                mstore(/** @src 1:1460:1461  "4" */ add(headStart, 64), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ iszero(iszero(value2)))
                mstore(/** @src 1:1460:1461  "4" */ add(headStart, 96), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ iszero(iszero(value3)))
                mstore(/** @src 1:1460:1461  "4" */ add(headStart, 128), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ iszero(iszero(value4)))
            }
            /// @ast-id 1115 @src 3:1471:1559  "function toUInt8(bool x) internal pure returns (uint8) {..."
            function fun_toUInt8(var_x) -> var
            {
                /// @src 3:1543:1552  "x ? 1 : 0"
                let expr := /** @src -1:-1:-1 */ 0
                /// @src 3:1543:1552  "x ? 1 : 0"
                switch var_x
                case 0 {
                    expr := /** @src -1:-1:-1 */ expr
                }
                default /// @src 3:1543:1552  "x ? 1 : 0"
                {
                    expr := /** @src 3:1547:1548  "1" */ 0x01
                }
                /// @src 3:1536:1552  "return x ? 1 : 0"
                var := expr
            }
            /// @ast-id 2672 @src 5:21684:21802  "function mulFactor(uint n, uint factor) internal pure returns (uint) {..."
            function fun_mulFactor(var_n, var_factor) -> var
            {
                /// @src 5:21763:21795  "return n * factor / FACTOR_SCALE"
                var := /** @src 1:2135:2139  "1e18" */ div(/** @src 5:21770:21780  "n * factor" */ checked_mul_uint256(var_n, var_factor), /** @src 1:2135:2139  "1e18" */ 0x0de0b6b3a7640000)
            }
            /// @ast-id 2689 @src 5:21873:21991  "function divBaseWei(uint n, uint baseWei) internal view returns (uint) {..."
            function fun_divBaseWei(var_n, var_baseWei) -> var
            {
                /// @src 5:21961:21974  "n * baseScale"
                let _1 := checked_mul_uint256(var_n, /** @src 5:21965:21974  "baseScale" */ loadimmutable("1305"))
                /// @src 1:2135:2139  "1e18"
                if iszero(var_baseWei) { panic_error_0x12() }
                /// @src 5:21954:21984  "return n * baseScale / baseWei"
                var := /** @src 1:2135:2139  "1e18" */ div(_1, var_baseWei)
            }
            /// @ast-id 2708 @src 5:22103:22233  "function mulPrice(uint n, uint price, uint64 fromScale) internal pure returns (uint) {..."
            function fun_mulPrice(var_n, var_price, var_fromScale) -> var
            {
                /// @src 5:22205:22214  "n * price"
                let expr := checked_mul_uint256(var_n, var_price)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _1 := and(/** @src 5:22205:22226  "n * price / fromScale" */ var_fromScale, /** @src 1:1927:1931  "1e15" */ sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1))
                /// @src 1:2135:2139  "1e18"
                if iszero(_1) { panic_error_0x12() }
                /// @src 5:22198:22226  "return n * price / fromScale"
                var := /** @src 1:2135:2139  "1e18" */ div(expr, _1)
            }
            /// @ast-id 2735 @src 5:22352:22514  "function signedMulPrice(int n, uint price, uint64 fromScale) internal pure returns (int) {..."
            function fun_signedMulPrice(var_n, var_price, var_fromScale) -> var
            {
                /// @src 5:22462:22478  "signed256(price)"
                let _1 := fun_signed256(var_price)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _2 := sub(shl(255, 1), 1)
                let _3 := sgt(_1, /** @src -1:-1:-1 */ 0)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _4 := sgt(var_n, /** @src -1:-1:-1 */ 0)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                if and(and(_4, _3), gt(var_n, div(_2, _1))) { panic_error_0x11() }
                let _5 := shl(255, 1)
                let _6 := slt(_1, /** @src -1:-1:-1 */ 0)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                if and(and(_4, _6), slt(_1, sdiv(_5, var_n))) { panic_error_0x11() }
                let _7 := slt(var_n, /** @src -1:-1:-1 */ 0)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                if and(and(_7, _3), slt(var_n, sdiv(_5, _1))) { panic_error_0x11() }
                if and(and(_7, _6), slt(var_n, sdiv(_2, _1))) { panic_error_0x11() }
                let product := mul(var_n, _1)
                let _8 := and(/** @src 5:22488:22506  "uint256(fromScale)" */ var_fromScale, /** @src 1:1927:1931  "1e15" */ sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1))
                if iszero(_8) { panic_error_0x12() }
                if and(eq(product, _5), eq(_8, not(0))) { panic_error_0x11() }
                /// @src 5:22451:22507  "return n * signed256(price) / int256(uint256(fromScale))"
                var := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sdiv(product, _8)
            }
            function checked_sub_uint8(x, y) -> diff
            {
                let x_1 := and(x, 0xff)
                let y_1 := and(y, 0xff)
                if lt(x_1, y_1) { panic_error_0x11() }
                diff := sub(x_1, y_1)
            }
            function shift_left_uint16_uint8(value, bits) -> result
            {
                let _1 := 0xffff
                result := and(/** @src 1:1247:1248  "0" */ shl(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(bits, 0xff), and(value, _1)), _1)
            }
            /// @ast-id 2808 @src 5:22914:23413  "function isInAsset(uint16 assetsIn, uint8 assetOffset, uint8 _reserved) internal pure returns (bool) {..."
            function fun_isInAsset(var_assetsIn, var_assetOffset, var_reserved) -> var
            {
                /// @src 5:23029:23045  "assetOffset < 16"
                let _1 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:23029:23045  "assetOffset < 16" */ var_assetOffset, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0xff)
                /// @src 5:23025:23341  "if (assetOffset < 16) {..."
                switch /** @src 5:23029:23045  "assetOffset < 16" */ lt(_1, /** @src 5:23043:23045  "16" */ 0x10)
                case /** @src 5:23025:23341  "if (assetOffset < 16) {..." */ 0 {
                    /// @src 5:23182:23341  "if (assetOffset < 24) {..."
                    if /** @src 5:23186:23202  "assetOffset < 24" */ lt(_1, /** @src 5:23200:23202  "24" */ 0x18)
                    /// @src 5:23182:23341  "if (assetOffset < 24) {..."
                    {
                        /// @src 5:23272:23330  "return (_reserved & (uint8(1) << (assetOffset - 16))) != 0"
                        var := /** @src 5:23279:23330  "(_reserved & (uint8(1) << (assetOffset - 16))) != 0" */ iszero(iszero(/** @src 5:23280:23324  "_reserved & (uint8(1) << (assetOffset - 16))" */ and(and(var_reserved, /** @src 1:1247:1248  "0" */ shl(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(add(_1, not(15)), 0xff), /** @src 5:23299:23300  "1" */ 0x01)), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0xff)))
                        /// @src 5:23272:23330  "return (_reserved & (uint8(1) << (assetOffset - 16))) != 0"
                        leave
                    }
                }
                default /// @src 5:23025:23341  "if (assetOffset < 16) {..."
                {
                    /// @src 5:23114:23165  "return (assetsIn & (uint16(1) << assetOffset)) != 0"
                    var := /** @src 5:23121:23165  "(assetsIn & (uint16(1) << assetOffset)) != 0" */ iszero(iszero(/** @src 5:23122:23159  "assetsIn & (uint16(1) << assetOffset)" */ and(and(var_assetsIn, /** @src 1:1247:1248  "0" */ shl(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1, /** @src 5:23141:23142  "1" */ 0x01)), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0xffff)))
                    /// @src 5:23114:23165  "return (assetsIn & (uint16(1) << assetOffset)) != 0"
                    leave
                }
                /// @src 5:23350:23362  "return false"
                var := /** @src 5:23357:23362  "false" */ 0x00
            }
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            function checked_sub_uint64(x, y) -> diff
            {
                let _1 := /** @src 1:1927:1931  "1e15" */ sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)
                let x_1 := and(x, _1)
                let y_1 := and(y, _1)
                if lt(x_1, y_1) { panic_error_0x11() }
                diff := sub(x_1, y_1)
            }
            function update_storage_value_offsett_uint16_to_uint16(slot, value)
            {
                let _1 := sload(slot)
                sstore(slot, or(and(_1, not(shl(232, 65535))), and(shl(232, value), shl(232, 65535))))
            }
            function copy_struct_to_storage_from_struct_UserBasic_to_struct_UserBasic(slot, value)
            {
                let _1 := mload(value)
                let _2 := sload(slot)
                let _3 := sub(shl(104, 1), 1)
                sstore(slot, or(and(_2, not(sub(shl(104, 1), 1))), and(_3, _1)))
                let _4 := and(shl(104, mload(add(value, 32))), sub(shl(168, 1), shl(104, 1)))
                let _5 := and(_1, _3)
                sstore(slot, or(or(and(_2, not(sub(shl(168, 1), 1))), _5), _4))
                sstore(slot, or(or(_4, or(and(_2, shl(232, 16777215)), _5)), and(shl(168, mload(add(value, 64))), sub(shl(232, 1), shl(168, 1)))))
                update_storage_value_offsett_uint16_to_uint16(slot, and(mload(add(value, 96)), 0xffff))
                update_storage_value_offsett_uint8_to_uint8(slot, and(mload(add(value, 128)), 0xff))
            }
            /// @ast-id 3036 @src 5:24759:25649  "function updateBasePrincipal(address account, UserBasic memory basic, int104 principalNew) internal {..."
            function fun_updateBasePrincipal(var_account, var_basic_mpos, var_principalNew)
            {
                /// @src 5:24888:24903  "basic.principal"
                let _1 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_from_storage_int104(mload(/** @src 5:24888:24903  "basic.principal" */ var_basic_mpos))
                /// @src 5:24913:24943  "basic.principal = principalNew"
                write_to_memory_int104(var_basic_mpos, var_principalNew)
                /// @src 5:24888:24903  "basic.principal"
                let _2 := 0
                /// @src 5:24954:25427  "if (principal >= 0) {..."
                switch /** @src 5:24958:24972  "principal >= 0" */ iszero(slt(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ signextend(12, /** @src 5:24958:24972  "principal >= 0" */ _1), /** @src 5:24888:24903  "basic.principal" */ _2))
                case /** @src 5:24954:25427  "if (principal >= 0) {..." */ 0 {
                    /// @src 5:25243:25262  "trackingBorrowIndex"
                    let _3 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ extract_from_storage_value_offset_24t_uint64(sload(/** @src 5:24888:24903  "basic.principal" */ _2))
                    /// @src 5:25339:25371  "uint104(-principal) * indexDelta"
                    let expr := checked_mul_uint256(extract_from_storage_value_offsett_uint104(/** @src 5:25339:25358  "uint104(-principal)" */ convert_int104_to_uint104(/** @src 5:25347:25357  "-principal" */ negate_int104(_1))), /** @src 5:25235:25289  "uint256(trackingBorrowIndex - basic.baseTrackingIndex)" */ cleanup_uint64(/** @src 5:25243:25288  "trackingBorrowIndex - basic.baseTrackingIndex" */ checked_sub_uint64(_3, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_uint64(mload(/** @src 5:25265:25288  "basic.baseTrackingIndex" */ add(var_basic_mpos, 32))))))
                    /// @src 5:25339:25392  "uint104(-principal) * indexDelta / trackingIndexScale"
                    let expr_1 := checked_div_uint256(expr, /** @src 5:25374:25392  "trackingIndexScale" */ loadimmutable("1309"))
                    /// @src 5:25332:25416  "safe64(uint104(-principal) * indexDelta / trackingIndexScale / accrualDescaleFactor)"
                    let expr_2 := fun_safe64(/** @src 5:25339:25415  "uint104(-principal) * indexDelta / trackingIndexScale / accrualDescaleFactor" */ checked_div_uint256(expr_1, /** @src 5:25395:25415  "accrualDescaleFactor" */ loadimmutable("1340")))
                    /// @src 5:25303:25328  "basic.baseTrackingAccrued"
                    let _4 := add(var_basic_mpos, 64)
                    /// @src 5:25303:25416  "basic.baseTrackingAccrued += safe64(uint104(-principal) * indexDelta / trackingIndexScale / accrualDescaleFactor)"
                    write_to_memory_uint64(_4, checked_add_uint64(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_uint64(mload(/** @src 5:25303:25416  "basic.baseTrackingAccrued += safe64(uint104(-principal) * indexDelta / trackingIndexScale / accrualDescaleFactor)" */ _4)), expr_2))
                }
                default /// @src 5:24954:25427  "if (principal >= 0) {..."
                {
                    /// @src 5:25014:25033  "trackingSupplyIndex"
                    let _5 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ extract_from_storage_value_offsett_uint64(sload(/** @src 5:24888:24903  "basic.principal" */ _2))
                    /// @src 5:25110:25141  "uint104(principal) * indexDelta"
                    let expr_3 := checked_mul_uint256(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:24958:24972  "principal >= 0" */ _1, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(shl(104, 1), 1)), /** @src 5:25006:25060  "uint256(trackingSupplyIndex - basic.baseTrackingIndex)" */ cleanup_uint64(/** @src 5:25014:25059  "trackingSupplyIndex - basic.baseTrackingIndex" */ checked_sub_uint64(_5, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_uint64(mload(/** @src 5:25036:25059  "basic.baseTrackingIndex" */ add(var_basic_mpos, 32))))))
                    /// @src 5:25110:25162  "uint104(principal) * indexDelta / trackingIndexScale"
                    let expr_4 := checked_div_uint256(expr_3, /** @src 5:25144:25162  "trackingIndexScale" */ loadimmutable("1309"))
                    /// @src 5:25103:25186  "safe64(uint104(principal) * indexDelta / trackingIndexScale / accrualDescaleFactor)"
                    let expr_5 := fun_safe64(/** @src 5:25110:25185  "uint104(principal) * indexDelta / trackingIndexScale / accrualDescaleFactor" */ checked_div_uint256(expr_4, /** @src 5:25165:25185  "accrualDescaleFactor" */ loadimmutable("1340")))
                    /// @src 5:25074:25099  "basic.baseTrackingAccrued"
                    let _6 := add(var_basic_mpos, 64)
                    /// @src 5:25074:25186  "basic.baseTrackingAccrued += safe64(uint104(principal) * indexDelta / trackingIndexScale / accrualDescaleFactor)"
                    write_to_memory_uint64(_6, checked_add_uint64(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_uint64(mload(/** @src 5:25074:25186  "basic.baseTrackingAccrued += safe64(uint104(principal) * indexDelta / trackingIndexScale / accrualDescaleFactor)" */ _6)), expr_5))
                }
                /// @src 5:25437:25606  "if (principalNew >= 0) {..."
                switch /** @src 5:25441:25458  "principalNew >= 0" */ iszero(slt(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ signextend(12, /** @src 5:25441:25458  "principalNew >= 0" */ var_principalNew), /** @src 5:24888:24903  "basic.principal" */ _2))
                case /** @src 5:25437:25606  "if (principalNew >= 0) {..." */ 0 {
                    /// @src 5:25550:25595  "basic.baseTrackingIndex = trackingBorrowIndex"
                    write_to_memory_uint64(/** @src 5:25550:25573  "basic.baseTrackingIndex" */ add(var_basic_mpos, 32), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ extract_from_storage_value_offset_24t_uint64(sload(/** @src 5:24888:24903  "basic.principal" */ _2)))
                }
                default /// @src 5:25437:25606  "if (principalNew >= 0) {..."
                {
                    /// @src 5:25474:25519  "basic.baseTrackingIndex = trackingSupplyIndex"
                    write_to_memory_uint64(/** @src 5:25474:25497  "basic.baseTrackingIndex" */ add(var_basic_mpos, 32), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ extract_from_storage_value_offsett_uint64(sload(/** @src 5:24888:24903  "basic.principal" */ _2)))
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                copy_struct_to_storage_from_struct_UserBasic_to_struct_UserBasic(/** @src 5:25616:25634  "userBasic[account]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:25616:25625  "userBasic" */ 0x05, /** @src 5:25616:25634  "userBasic[account]" */ var_account), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ var_basic_mpos)
            }
            /// @src 5:29500:30032  "function supplyInternal(address operator, address from, address dst, address asset, uint amount) internal nonReentrant {..."
            function fun_supplyInternal_inner(var_operator, var_from, var_dst, var_asset, var_amount)
            {
                /// @src 5:29629:29666  "if (isSupplyPaused()) revert Paused()"
                if /** @src 3:1636:1642  "x != 0" */ iszero(iszero(/** @src 5:20691:20737  "pauseFlags & (uint8(1) << PAUSE_SUPPLY_OFFSET)" */ and(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ shr(248, sload(/** @src 5:20691:20701  "pauseFlags" */ 0x01)), 0x01)))
                /// @src 5:29629:29666  "if (isSupplyPaused()) revert Paused()"
                {
                    /// @src 5:29658:29666  "Paused()"
                    let _1 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 5:29658:29666  "Paused()"
                    mstore(_1, /** @src 5:45320:45328  "Paused()" */ shl(227, 0x13d0ff59))
                    /// @src 5:29658:29666  "Paused()"
                    revert(_1, 4)
                }
                /// @src 5:29676:29733  "if (!hasPermission(from, operator)) revert Unauthorized()"
                if /** @src 5:29680:29710  "!hasPermission(from, operator)" */ cleanup_bool(iszero(/** @src 5:29681:29710  "hasPermission(from, operator)" */ fun_hasPermission(var_from, var_operator)))
                /// @src 5:29676:29733  "if (!hasPermission(from, operator)) revert Unauthorized()"
                {
                    /// @src 5:29719:29733  "Unauthorized()"
                    let _2 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 5:29719:29733  "Unauthorized()"
                    mstore(_2, /** @src 5:20057:20071  "Unauthorized()" */ shl(232, 8565801))
                    /// @src 5:29719:29733  "Unauthorized()"
                    revert(_2, 4)
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _3 := sub(shl(160, 1), 1)
                /// @src 5:29744:30026  "if (asset == baseToken) {..."
                switch /** @src 5:29748:29766  "asset == baseToken" */ eq(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:29748:29766  "asset == baseToken" */ var_asset, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _3), and(/** @src 5:29757:29766  "baseToken" */ loadimmutable("1257"), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _3))
                case /** @src 5:29744:30026  "if (asset == baseToken) {..." */ 0 {
                    /// @src 5:29999:30014  "safe128(amount)"
                    fun_supplyCollateral(var_from, var_dst, var_asset, fun_safe128(var_amount))
                    /// @src 5:29957:30015  "return supplyCollateral(from, dst, asset, safe128(amount))"
                    leave
                }
                default /// @src 5:29744:30026  "if (asset == baseToken) {..."
                {
                    /// @src 5:29782:29877  "if (amount == type(uint256).max) {..."
                    if /** @src 5:29786:29813  "amount == type(uint256).max" */ eq(var_amount, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ not(0))
                    /// @src 5:29782:29877  "if (amount == type(uint256).max) {..."
                    {
                        /// @src 5:29833:29862  "amount = borrowBalanceOf(dst)"
                        var_amount := /** @src 5:29842:29862  "borrowBalanceOf(dst)" */ fun_borrowBalanceOf(var_dst)
                    }
                    /// @src 5:29919:29925  "amount"
                    fun_supplyBase(var_from, var_dst, var_amount)
                    /// @src 5:29890:29926  "return supplyBase(from, dst, amount)"
                    leave
                }
            }
            /// @ast-id 1008 @src 3:686:837  "function safe128(uint n) internal pure returns (uint128) {..."
            function fun_safe128(var_n) -> var
            {
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _1 := /** @src 1:1927:1931  "1e15" */ sub(shl(128, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)
                /// @src 3:753:803  "if (n > type(uint128).max) revert InvalidUInt128()"
                if /** @src 3:757:778  "n > type(uint128).max" */ gt(var_n, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1)
                /// @src 3:753:803  "if (n > type(uint128).max) revert InvalidUInt128()"
                {
                    /// @src 3:787:803  "InvalidUInt128()"
                    let _2 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 3:787:803  "InvalidUInt128()"
                    mstore(_2, shl(225, 0x762ea711))
                    revert(_2, 4)
                }
                /// @src 3:813:830  "return uint128(n)"
                var := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 3:820:830  "uint128(n)" */ var_n, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1)
            }
            /// @ast-id 1602 @src 5:7534:7910  "function nonReentrantBefore() internal {..."
            function fun_nonReentrantBefore()
            {
                /// @src 1:2266:2301  "keccak256(\"comet.reentrancy.guard\")"
                let _1 := 0xc98c7730ba19013824f711a9ab74801459b27e6ff7685cb924587c89aeda53ac
                /// @src 5:7738:7807  "if (status == REENTRANCY_GUARD_ENTERED) revert ReentrantCallBlocked()"
                if /** @src 5:7742:7776  "status == REENTRANCY_GUARD_ENTERED" */ eq(/** @src 5:7658:7728  "assembly (\"memory-safe\") {..." */ sload(/** @src 1:2266:2301  "keccak256(\"comet.reentrancy.guard\")" */ _1), /** @src 1:2469:2470  "1" */ 0x01)
                /// @src 5:7738:7807  "if (status == REENTRANCY_GUARD_ENTERED) revert ReentrantCallBlocked()"
                {
                    /// @src 5:7785:7807  "ReentrantCallBlocked()"
                    let _2 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 5:7785:7807  "ReentrantCallBlocked()"
                    mstore(_2, shl(226, 0x139b6435))
                    revert(_2, 4)
                }
                /// @src 5:7817:7904  "assembly (\"memory-safe\") {..."
                sstore(/** @src 1:2266:2301  "keccak256(\"comet.reentrancy.guard\")" */ _1, /** @src 1:2469:2470  "1" */ 0x01)
            }
            /// @ast-id 1615 @src 5:7971:8191  "function nonReentrantAfter() internal {..."
            function fun_nonReentrantAfter()
            {
                /// @src 5:8094:8185  "assembly (\"memory-safe\") {..."
                sstore(/** @src 1:2266:2301  "keccak256(\"comet.reentrancy.guard\")" */ 0xc98c7730ba19013824f711a9ab74801459b27e6ff7685cb924587c89aeda53ac, /** @src -1:-1:-1 */ 0)
            }
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            function checked_add_uint104(x, y) -> sum
            {
                let _1 := sub(shl(104, 1), 1)
                let x_1 := and(x, _1)
                let y_1 := and(y, _1)
                if gt(x_1, sub(_1, y_1)) { panic_error_0x11() }
                sum := add(x_1, y_1)
            }
            function update_storage_value_offsett_uint104_to_t_uint104(slot, value)
            {
                sstore(slot, or(and(sload(slot), not(sub(shl(104, 1), 1))), and(value, sub(shl(104, 1), 1))))
            }
            function checked_sub_uint104(x, y) -> diff
            {
                let _1 := sub(shl(104, 1), 1)
                let x_1 := and(x, _1)
                let y_1 := and(y, _1)
                if lt(x_1, y_1) { panic_error_0x11() }
                diff := sub(x_1, y_1)
            }
            function update_storage_value_offsett_uint104_to_uint104(slot, value)
            {
                let _1 := sload(slot)
                sstore(slot, or(and(_1, not(sub(shl(208, 1), shl(104, 1)))), and(shl(104, value), sub(shl(208, 1), shl(104, 1)))))
            }
            /// @ast-id 3354 @src 5:30116:30946  "function supplyBase(address from, address dst, uint256 amount) internal {..."
            function fun_supplyBase(var_from, var_dst, var_amount)
            {
                /// @src 5:30207:30244  "doTransferIn(baseToken, from, amount)"
                let expr := fun_doTransferIn(/** @src 5:30220:30229  "baseToken" */ loadimmutable("1257"), /** @src 5:30207:30244  "doTransferIn(baseToken, from, amount)" */ var_from, var_amount)
                /// @src 5:30198:30244  "amount = doTransferIn(baseToken, from, amount)"
                fun_accrueInternal()
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let converted := read_from_storage_reference_type_struct_UserBasic(/** @src 5:30309:30323  "userBasic[dst]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:30309:30318  "userBasic" */ 0x05, /** @src 5:30309:30323  "userBasic[dst]" */ var_dst))
                /// @src 5:30355:30372  "dstUser.principal"
                let _1 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_from_storage_int104(mload(/** @src 5:30355:30372  "dstUser.principal" */ converted))
                /// @src 5:30402:30428  "presentValue(dstPrincipal)"
                let expr_1 := fun_presentValue(_1)
                /// @src 5:30483:30509  "principalValue(dstBalance)"
                let expr_2 := fun_principalValue(/** @src 5:30402:30448  "presentValue(dstPrincipal) + signed256(amount)" */ checked_add_int256(expr_1, /** @src 5:30431:30448  "signed256(amount)" */ fun_signed256(expr)))
                /// @src 5:30566:30617  "repayAndSupplyAmount(dstPrincipal, dstPrincipalNew)"
                let expr_3314_component, expr_3314_component_1 := fun_repayAndSupplyAmount(_1, expr_2)
                /// @src 5:30628:30659  "totalSupplyBase += supplyAmount"
                update_storage_value_offsett_uint104_to_t_uint104(0x01, checked_add_uint104(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ extract_from_storage_value_offsett_uint104(sload(/** @src 5:30628:30659  "totalSupplyBase += supplyAmount" */ 0x01)), expr_3314_component_1))
                /// @src 5:30669:30699  "totalBorrowBase -= repayAmount"
                update_storage_value_offsett_uint104_to_uint104(/** @src 5:30628:30659  "totalSupplyBase += supplyAmount" */ 0x01, /** @src 5:30669:30699  "totalBorrowBase -= repayAmount" */ checked_sub_uint104(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ extract_from_storage_value_offset_13t_uint104(sload(/** @src 5:30628:30659  "totalSupplyBase += supplyAmount" */ 0x01)), /** @src 5:30669:30699  "totalBorrowBase -= repayAmount" */ expr_3314_component))
                /// @src 5:30744:30759  "dstPrincipalNew"
                fun_updateBasePrincipal(var_dst, converted, expr_2)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _2 := sub(shl(160, 1), 1)
                let _3 := and(/** @src 5:30776:30801  "Supply(from, dst, amount)" */ var_dst, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _2)
                /// @src 5:30776:30801  "Supply(from, dst, amount)"
                let _4 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                /// @src 5:30776:30801  "Supply(from, dst, amount)"
                log3(_4, sub(abi_encode_uint256(_4, expr), _4), 0xd1cf3d156d5f8f0d50f6c122ed609cec09d35c9b9fb3fff6ea0959134dae424e, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:30776:30801  "Supply(from, dst, amount)" */ var_from, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _2), /** @src 5:30776:30801  "Supply(from, dst, amount)" */ _3)
                /// @src 5:30812:30940  "if (supplyAmount > 0) {..."
                if /** @src 5:30816:30832  "supplyAmount > 0" */ iszero(iszero(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:30816:30832  "supplyAmount > 0" */ expr_3314_component_1, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(shl(104, 1), 1))))
                /// @src 5:30812:30940  "if (supplyAmount > 0) {..."
                {
                    /// @src 5:30879:30928  "presentValueSupply(baseSupplyIndex, supplyAmount)"
                    let expr_3 := fun_presentValueSupply(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_uint64(sload(/** @src -1:-1:-1 */ 0)), /** @src 5:30879:30928  "presentValueSupply(baseSupplyIndex, supplyAmount)" */ expr_3314_component_1)
                    /// @src 5:30853:30929  "Transfer(address(0), dst, presentValueSupply(baseSupplyIndex, supplyAmount))"
                    let _5 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 5:30853:30929  "Transfer(address(0), dst, presentValueSupply(baseSupplyIndex, supplyAmount))"
                    log3(_5, sub(abi_encode_uint256(_5, expr_3), _5), 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef, /** @src -1:-1:-1 */ 0, /** @src 5:30853:30929  "Transfer(address(0), dst, presentValueSupply(baseSupplyIndex, supplyAmount))" */ _3)
                }
            }
            /// @ast-id 304 @src 1:4011:4344  "function principalValue(int256 presentValue_) internal view returns (int104) {..."
            function fun_principalValue(var_presentValue) -> var
            {
                /// @src 1:4098:4338  "if (presentValue_ >= 0) {..."
                switch /** @src 1:4102:4120  "presentValue_ >= 0" */ iszero(slt(var_presentValue, /** @src 1:4119:4120  "0" */ 0x00))
                case /** @src 1:4098:4338  "if (presentValue_ >= 0) {..." */ 0 {
                    /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                    let value := and(shr(64, sload(/** @src 1:4119:4120  "0" */ 0x00)), /** @src 1:1927:1931  "1e15" */ sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1))
                    /// @src 1:4310:4324  "-presentValue_"
                    let _1 := negate_int256(var_presentValue)
                    /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                    let _2 := not(0)
                    /// @src 1:1927:1931  "1e15"
                    let _3 := 0x038d7ea4c68000
                    /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                    if and(iszero(iszero(_1)), gt(/** @src 1:1927:1931  "1e15" */ _3, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ div(_2, _1))) { panic_error_0x11() }
                    /// @src 1:5102:5153  "presentValue_ * BASE_INDEX_SCALE + baseBorrowIndex_"
                    let expr := checked_add_uint256(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mul(_1, /** @src 1:1927:1931  "1e15" */ _3), /** @src 1:5102:5153  "presentValue_ * BASE_INDEX_SCALE + baseBorrowIndex_" */ value)
                    /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                    if lt(expr, /** @src 1:5156:5157  "1" */ 0x01)
                    /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                    { panic_error_0x11() }
                    /// @src 1:2135:2139  "1e18"
                    if iszero(value) { panic_error_0x12() }
                    /// @src 1:4246:4327  "return -signed104(principalValueBorrow(baseBorrowIndex, uint256(-presentValue_)))"
                    var := /** @src 1:4253:4327  "-signed104(principalValueBorrow(baseBorrowIndex, uint256(-presentValue_)))" */ negate_int104(/** @src 1:4254:4327  "signed104(principalValueBorrow(baseBorrowIndex, uint256(-presentValue_)))" */ fun_signed104(/** @src 1:5093:5178  "safe104((presentValue_ * BASE_INDEX_SCALE + baseBorrowIndex_ - 1) / baseBorrowIndex_)" */ fun_safe104(/** @src 1:2135:2139  "1e18" */ div(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ add(expr, _2), /** @src 1:2135:2139  "1e18" */ value))))
                    /// @src 1:4246:4327  "return -signed104(principalValueBorrow(baseBorrowIndex, uint256(-presentValue_)))"
                    leave
                }
                default /// @src 1:4098:4338  "if (presentValue_ >= 0) {..."
                {
                    /// @src 1:4136:4215  "return signed104(principalValueSupply(baseSupplyIndex, uint256(presentValue_)))"
                    var := /** @src 1:4143:4215  "signed104(principalValueSupply(baseSupplyIndex, uint256(presentValue_)))" */ fun_signed104(/** @src 1:4153:4214  "principalValueSupply(baseSupplyIndex, uint256(presentValue_))" */ fun_principalValueSupply(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(sload(/** @src 1:4119:4120  "0" */ 0x00), /** @src 1:1927:1931  "1e15" */ sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)), /** @src 1:4191:4213  "uint256(presentValue_)" */ var_presentValue))
                    /// @src 1:4136:4215  "return signed104(principalValueSupply(baseSupplyIndex, uint256(presentValue_)))"
                    leave
                }
            }
            /// @ast-id 324 @src 1:4558:4754  "function principalValueSupply(uint64 baseSupplyIndex_, uint256 presentValue_) internal pure returns (uint104) {..."
            function fun_principalValueSupply(var_baseSupplyIndex, var_presentValue) -> var
            {
                /// @src 1:1927:1931  "1e15"
                let _1 := 0x038d7ea4c68000
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                if and(iszero(iszero(var_presentValue)), gt(/** @src 1:1927:1931  "1e15" */ _1, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ div(not(0), var_presentValue))) { panic_error_0x11() }
                let _2 := and(/** @src 1:4693:4746  "(presentValue_ * BASE_INDEX_SCALE) / baseSupplyIndex_" */ var_baseSupplyIndex, /** @src 1:1927:1931  "1e15" */ sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1))
                /// @src 1:2135:2139  "1e18"
                if iszero(_2) { panic_error_0x12() }
                /// @src 1:4678:4747  "return safe104((presentValue_ * BASE_INDEX_SCALE) / baseSupplyIndex_)"
                var := /** @src 1:4685:4747  "safe104((presentValue_ * BASE_INDEX_SCALE) / baseSupplyIndex_)" */ fun_safe104(/** @src 1:2135:2139  "1e18" */ div(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mul(var_presentValue, /** @src 1:1927:1931  "1e15" */ _1), /** @src 1:2135:2139  "1e18" */ _2))
            }
            /// @ast-id 984 @src 3:529:680  "function safe104(uint n) internal pure returns (uint104) {..."
            function fun_safe104(var_n) -> var
            {
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _1 := sub(shl(104, 1), 1)
                /// @src 3:596:646  "if (n > type(uint104).max) revert InvalidUInt104()"
                if /** @src 3:600:621  "n > type(uint104).max" */ gt(var_n, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1)
                /// @src 3:596:646  "if (n > type(uint104).max) revert InvalidUInt104()"
                {
                    /// @src 3:630:646  "InvalidUInt104()"
                    let _2 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 3:630:646  "InvalidUInt104()"
                    mstore(_2, shl(225, 0x0dc79255))
                    revert(_2, 4)
                }
                /// @src 3:656:673  "return uint104(n)"
                var := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 3:663:673  "uint104(n)" */ var_n, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1)
            }
            /// @ast-id 1035 @src 3:843:1004  "function signed104(uint104 n) internal pure returns (int104) {..."
            function fun_signed104(var_n) -> var
            {
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _1 := and(/** @src 3:918:947  "n > uint104(type(int104).max)" */ var_n, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(shl(104, 1), 1))
                /// @src 3:914:971  "if (n > uint104(type(int104).max)) revert InvalidInt104()"
                if /** @src 3:918:947  "n > uint104(type(int104).max)" */ gt(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1, sub(shl(103, 1), 1))
                /// @src 3:914:971  "if (n > uint104(type(int104).max)) revert InvalidInt104()"
                {
                    /// @src 3:956:971  "InvalidInt104()"
                    let _2 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 3:956:971  "InvalidInt104()"
                    mstore(_2, shl(224, 0x9369ae35))
                    revert(_2, 4)
                }
                /// @src 3:981:997  "return int104(n)"
                var := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ signextend(12, _1)
            }
            function checked_sub_int104(x, y) -> diff
            {
                let x_1 := signextend(12, x)
                let y_1 := signextend(12, y)
                let _1 := slt(y_1, 0)
                if and(iszero(_1), slt(x_1, add(not(sub(shl(103, 1), 1)), y_1))) { panic_error_0x11() }
                if and(_1, sgt(x_1, add(sub(shl(103, 1), 1), y_1))) { panic_error_0x11() }
                diff := sub(x_1, y_1)
            }
            /// @ast-id 2415 @src 5:18160:18736  "function repayAndSupplyAmount(int104 oldPrincipal, int104 newPrincipal) internal pure returns (uint104, uint104) {..."
            function fun_repayAndSupplyAmount(var_oldPrincipal, var_newPrincipal) -> var, var_1
            {
                /// @src 5:18394:18421  "newPrincipal < oldPrincipal"
                let _1 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ signextend(12, /** @src 5:18394:18421  "newPrincipal < oldPrincipal" */ var_oldPrincipal)
                let _2 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ signextend(12, /** @src 5:18394:18421  "newPrincipal < oldPrincipal" */ var_newPrincipal)
                /// @src 5:18390:18436  "if (newPrincipal < oldPrincipal) return (0, 0)"
                if /** @src 5:18394:18421  "newPrincipal < oldPrincipal" */ slt(_2, _1)
                /// @src 5:18390:18436  "if (newPrincipal < oldPrincipal) return (0, 0)"
                {
                    /// @src 5:18423:18436  "return (0, 0)"
                    var := /** @src 5:18431:18432  "0" */ 0x00
                    /// @src 5:18423:18436  "return (0, 0)"
                    var_1 := /** @src 5:18431:18432  "0" */ 0x00
                    /// @src 5:18423:18436  "return (0, 0)"
                    leave
                }
                /// @src 5:18447:18730  "if (newPrincipal <= 0) {..."
                switch /** @src 5:18451:18468  "newPrincipal <= 0" */ iszero(sgt(_2, /** @src 5:18467:18468  "0" */ 0x00))
                case /** @src 5:18447:18730  "if (newPrincipal <= 0) {..." */ 0 {
                    /// @src 5:18549:18730  "if (oldPrincipal >= 0) {..."
                    switch /** @src 5:18553:18570  "oldPrincipal >= 0" */ iszero(slt(_1, /** @src 5:18467:18468  "0" */ 0x00))
                    case /** @src 5:18549:18730  "if (oldPrincipal >= 0) {..." */ 0 {
                        /// @src 5:18681:18694  "-oldPrincipal"
                        let _3 := negate_int104(var_oldPrincipal)
                        /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                        let _4 := sub(shl(104, 1), 1)
                        /// @src 5:18665:18719  "return (uint104(-oldPrincipal), uint104(newPrincipal))"
                        var := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(_4, /** @src 5:18681:18694  "-oldPrincipal" */ _3)
                        /// @src 5:18665:18719  "return (uint104(-oldPrincipal), uint104(newPrincipal))"
                        var_1 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(_4, /** @src 5:18394:18421  "newPrincipal < oldPrincipal" */ var_newPrincipal)
                        /// @src 5:18665:18719  "return (uint104(-oldPrincipal), uint104(newPrincipal))"
                        leave
                    }
                    default /// @src 5:18549:18730  "if (oldPrincipal >= 0) {..."
                    {
                        /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                        let converted := and(sub(shl(104, 1), 1), /** @src 5:18605:18632  "newPrincipal - oldPrincipal" */ checked_sub_int104(var_newPrincipal, var_oldPrincipal))
                        /// @src 5:18586:18634  "return (0, uint104(newPrincipal - oldPrincipal))"
                        var := /** @src 5:18467:18468  "0" */ 0x00
                        /// @src 5:18586:18634  "return (0, uint104(newPrincipal - oldPrincipal))"
                        var_1 := converted
                        leave
                    }
                }
                default /// @src 5:18447:18730  "if (newPrincipal <= 0) {..."
                {
                    /// @src 5:18484:18532  "return (uint104(newPrincipal - oldPrincipal), 0)"
                    var := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(sub(shl(104, 1), 1), /** @src 5:18500:18527  "newPrincipal - oldPrincipal" */ checked_sub_int104(var_newPrincipal, var_oldPrincipal))
                    /// @src 5:18484:18532  "return (uint104(newPrincipal - oldPrincipal), 0)"
                    var_1 := /** @src 5:18467:18468  "0" */ 0x00
                    /// @src 5:18484:18532  "return (uint104(newPrincipal - oldPrincipal), 0)"
                    leave
                }
            }
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            function abi_encode_address_address_uint256(headStart, value0, value1, value2) -> tail
            {
                tail := add(headStart, 96)
                let _1 := sub(shl(160, 1), 1)
                mstore(headStart, and(value0, _1))
                mstore(add(headStart, 32), and(value1, _1))
                mstore(add(headStart, 64), value2)
            }
            /// @ast-id 3095 @src 5:25972:27035  "function doTransferIn(address asset, address from, uint amount) internal returns (uint) {..."
            function fun_doTransferIn(var_asset, var_from, var_amount) -> var
            {
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _1 := and(/** @src 5:26099:26123  "IERC20NonStandard(asset)" */ var_asset, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(shl(160, 1), 1))
                /// @src 5:26099:26148  "IERC20NonStandard(asset).balanceOf(address(this))"
                let _2 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                let _3 := shl(224, 0x70a08231)
                /// @src 5:26099:26148  "IERC20NonStandard(asset).balanceOf(address(this))"
                mstore(_2, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _3)
                /// @src 5:26099:26148  "IERC20NonStandard(asset).balanceOf(address(this))"
                let _4 := 32
                let _5 := staticcall(gas(), _1, _2, sub(abi_encode_address(add(_2, 4), /** @src 5:26142:26146  "this" */ address()), /** @src 5:26099:26148  "IERC20NonStandard(asset).balanceOf(address(this))" */ _2), _2, _4)
                if iszero(_5) { revert_forward() }
                let expr := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0
                /// @src 5:26099:26148  "IERC20NonStandard(asset).balanceOf(address(this))"
                if _5
                {
                    let _6 := _4
                    if gt(_4, returndatasize()) { _6 := returndatasize() }
                    finalize_allocation(_2, _6)
                    expr := abi_decode_uint256_fromMemory(_2, add(_2, _6))
                }
                /// @src 5:26158:26224  "IERC20NonStandard(asset).transferFrom(from, address(this), amount)"
                if iszero(extcodesize(_1))
                {
                    /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                    revert(0, 0)
                }
                /// @src 5:26158:26224  "IERC20NonStandard(asset).transferFrom(from, address(this), amount)"
                let _7 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                /// @src 5:26158:26224  "IERC20NonStandard(asset).transferFrom(from, address(this), amount)"
                mstore(_7, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ shl(224, 0x23b872dd))
                /// @src 5:26158:26224  "IERC20NonStandard(asset).transferFrom(from, address(this), amount)"
                let _8 := call(gas(), _1, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0, /** @src 5:26158:26224  "IERC20NonStandard(asset).transferFrom(from, address(this), amount)" */ _7, sub(abi_encode_address_address_uint256(add(_7, /** @src 5:26099:26148  "IERC20NonStandard(asset).balanceOf(address(this))" */ 4), /** @src 5:26158:26224  "IERC20NonStandard(asset).transferFrom(from, address(this), amount)" */ var_from, /** @src 5:26142:26146  "this" */ address(), /** @src 5:26158:26224  "IERC20NonStandard(asset).transferFrom(from, address(this), amount)" */ var_amount), _7), _7, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0)
                /// @src 5:26158:26224  "IERC20NonStandard(asset).transferFrom(from, address(this), amount)"
                if iszero(_8) { revert_forward() }
                if _8
                {
                    finalize_allocation(_7, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0)
                    /// @src 5:26158:26224  "IERC20NonStandard(asset).transferFrom(from, address(this), amount)"
                    abi_decode(_7, _7)
                }
                /// @src 5:26234:26246  "bool success"
                let var_success := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0
                /// @src 5:26256:26893  "assembly (\"memory-safe\") {..."
                switch returndatasize()
                case 0 {
                    var_success := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ not(0)
                }
                case /** @src 5:26256:26893  "assembly (\"memory-safe\") {..." */ 32 {
                    returndatacopy(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0, 0, /** @src 5:26099:26148  "IERC20NonStandard(asset).balanceOf(address(this))" */ _4)
                    /// @src 5:26256:26893  "assembly (\"memory-safe\") {..."
                    var_success := mload(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0)
                }
                default /// @src 5:26256:26893  "assembly (\"memory-safe\") {..."
                {
                    revert(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0, 0)
                }
                /// @src 5:26902:26941  "if (!success) revert TransferInFailed()"
                if /** @src 5:26906:26914  "!success" */ iszero(var_success)
                /// @src 5:26902:26941  "if (!success) revert TransferInFailed()"
                {
                    /// @src 5:26923:26941  "TransferInFailed()"
                    let _9 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 5:26923:26941  "TransferInFailed()"
                    mstore(_9, shl(229, 0x073d1efd))
                    revert(_9, /** @src 5:26099:26148  "IERC20NonStandard(asset).balanceOf(address(this))" */ 4)
                }
                /// @src 5:26958:27007  "IERC20NonStandard(asset).balanceOf(address(this))"
                let _10 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                /// @src 5:26958:27007  "IERC20NonStandard(asset).balanceOf(address(this))"
                mstore(_10, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _3)
                /// @src 5:26958:27007  "IERC20NonStandard(asset).balanceOf(address(this))"
                let _11 := staticcall(gas(), _1, _10, sub(abi_encode_address(add(_10, /** @src 5:26099:26148  "IERC20NonStandard(asset).balanceOf(address(this))" */ 4), /** @src 5:26142:26146  "this" */ address()), /** @src 5:26958:27007  "IERC20NonStandard(asset).balanceOf(address(this))" */ _10), _10, /** @src 5:26099:26148  "IERC20NonStandard(asset).balanceOf(address(this))" */ _4)
                /// @src 5:26958:27007  "IERC20NonStandard(asset).balanceOf(address(this))"
                if iszero(_11) { revert_forward() }
                let expr_1 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0
                /// @src 5:26958:27007  "IERC20NonStandard(asset).balanceOf(address(this))"
                if _11
                {
                    let _12 := /** @src 5:26099:26148  "IERC20NonStandard(asset).balanceOf(address(this))" */ _4
                    /// @src 5:26958:27007  "IERC20NonStandard(asset).balanceOf(address(this))"
                    if gt(/** @src 5:26099:26148  "IERC20NonStandard(asset).balanceOf(address(this))" */ _4, /** @src 5:26958:27007  "IERC20NonStandard(asset).balanceOf(address(this))" */ returndatasize()) { _12 := returndatasize() }
                    finalize_allocation(_10, _12)
                    expr_1 := abi_decode_uint256_fromMemory(_10, add(_10, _12))
                }
                /// @src 5:26951:27028  "return IERC20NonStandard(asset).balanceOf(address(this)) - preTransferBalance"
                var := /** @src 5:26958:27028  "IERC20NonStandard(asset).balanceOf(address(this)) - preTransferBalance" */ checked_sub_uint256(expr_1, expr)
            }
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            function write_to_memory_uint128(memPtr, value)
            {
                mstore(memPtr, and(value, /** @src 1:1927:1931  "1e15" */ sub(shl(128, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)))
            }
            function read_from_storage_reference_type_struct_TotalsCollateral(slot) -> value
            {
                let memPtr := mload(64)
                finalize_allocation(memPtr, 64)
                value := memPtr
                let _1 := sload(slot)
                mstore(memPtr, and(_1, /** @src 1:1927:1931  "1e15" */ sub(shl(128, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)))
                mstore(add(memPtr, 32), shr(128, _1))
            }
            function checked_add_uint128(x, y) -> sum
            {
                let _1 := /** @src 1:1927:1931  "1e15" */ sub(shl(128, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)
                let x_1 := and(x, _1)
                let y_1 := and(y, _1)
                if gt(x_1, sub(_1, y_1)) { panic_error_0x11() }
                sum := add(x_1, y_1)
            }
            function update_storage_value_offsett_uint128_to_uint128(slot, value)
            {
                sstore(slot, or(and(sload(slot), /** @src 1:1927:1931  "1e15" */ not(sub(shl(128, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1))), and(value, /** @src 1:1927:1931  "1e15" */ sub(shl(128, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1))))
            }
            function copy_struct_to_storage_from_struct_TotalsCollateral_to_struct_TotalsCollateral(slot, value)
            {
                let _1 := /** @src 1:1927:1931  "1e15" */ sub(shl(128, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)
                update_storage_value_offsett_uint128_to_uint128(slot, and(mload(value), _1))
                let _2 := mload(add(value, 32))
                let _3 := sload(slot)
                sstore(slot, or(and(_3, _1), and(shl(128, _2), /** @src 1:1927:1931  "1e15" */ not(sub(shl(128, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)))))
            }
            function abi_encode_tuple_uint128(headStart, value0) -> tail
            {
                tail := add(headStart, 32)
                mstore(headStart, and(value0, /** @src 1:1927:1931  "1e15" */ sub(shl(128, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)))
            }
            /// @ast-id 3450 @src 5:31036:31827  "function supplyCollateral(address from, address dst, address asset, uint128 amount) internal {..."
            function fun_supplyCollateral(var_from, var_dst, var_asset, var_amount)
            {
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _1 := /** @src 1:1927:1931  "1e15" */ sub(shl(128, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)
                /// @src 5:31148:31190  "safe128(doTransferIn(asset, from, amount))"
                let expr := fun_safe128(/** @src 5:31156:31189  "doTransferIn(asset, from, amount)" */ fun_doTransferIn(var_asset, var_from, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:31156:31189  "doTransferIn(asset, from, amount)" */ var_amount, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1)))
                /// @src 5:31230:31258  "getAssetInfoByAddress(asset)"
                let expr_3381_mpos := fun_getAssetInfoByAddress(var_asset)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let converted := read_from_storage_reference_type_struct_TotalsCollateral(/** @src 5:31301:31324  "totalsCollateral[asset]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:31301:31317  "totalsCollateral" */ 0x02, /** @src 5:31301:31324  "totalsCollateral[asset]" */ var_asset))
                /// @src 5:31334:31367  "totals.totalSupplyAsset += amount"
                write_to_memory_uint128(converted, checked_add_uint128(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_from_storage_uint128(mload(/** @src 5:31334:31367  "totals.totalSupplyAsset += amount" */ converted)), expr))
                /// @src 5:31381:31404  "totals.totalSupplyAsset"
                let _2 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_from_storage_uint128(mload(/** @src 5:31381:31404  "totals.totalSupplyAsset" */ converted))
                /// @src 5:31377:31454  "if (totals.totalSupplyAsset > assetInfo.supplyCap) revert SupplyCapExceeded()"
                if /** @src 5:31381:31426  "totals.totalSupplyAsset > assetInfo.supplyCap" */ gt(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:31381:31426  "totals.totalSupplyAsset > assetInfo.supplyCap" */ _2, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1), /** @src 5:31381:31426  "totals.totalSupplyAsset > assetInfo.supplyCap" */ cleanup_from_storage_uint128(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_from_storage_uint128(mload(/** @src 5:31407:31426  "assetInfo.supplyCap" */ add(expr_3381_mpos, 224)))))
                /// @src 5:31377:31454  "if (totals.totalSupplyAsset > assetInfo.supplyCap) revert SupplyCapExceeded()"
                {
                    /// @src 5:31435:31454  "SupplyCapExceeded()"
                    let _3 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 5:31435:31454  "SupplyCapExceeded()"
                    mstore(_3, shl(225, 0x7ac7b99d))
                    revert(_3, 4)
                }
                /// @src 5:31489:31523  "userCollateral[dst][asset].balance"
                let _4 := read_from_storage_split_offset_uint128(/** @src 5:31489:31515  "userCollateral[dst][asset]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:31489:31508  "userCollateral[dst]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:31489:31503  "userCollateral" */ 0x06, /** @src 5:31489:31508  "userCollateral[dst]" */ var_dst), /** @src 5:31489:31515  "userCollateral[dst][asset]" */ var_asset))
                /// @src 5:31560:31582  "dstCollateral + amount"
                let expr_1 := checked_add_uint128(_4, expr)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                copy_struct_to_storage_from_struct_TotalsCollateral_to_struct_TotalsCollateral(/** @src 5:31593:31616  "totalsCollateral[asset]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:31301:31317  "totalsCollateral" */ 0x02, /** @src 5:31593:31616  "totalsCollateral[asset]" */ var_asset), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ converted)
                /// @src 5:31635:31688  "userCollateral[dst][asset].balance = dstCollateralNew"
                update_storage_value_offsett_uint128_to_uint128(/** @src 5:31635:31661  "userCollateral[dst][asset]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:31635:31654  "userCollateral[dst]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:31489:31503  "userCollateral" */ 0x06, /** @src 5:31635:31654  "userCollateral[dst]" */ var_dst), /** @src 5:31635:31661  "userCollateral[dst][asset]" */ var_asset), /** @src 5:31635:31688  "userCollateral[dst][asset].balance = dstCollateralNew" */ expr_1)
                /// @src 5:31745:31761  "dstCollateralNew"
                fun_updateAssetsIn(var_dst, expr_3381_mpos, _4, expr_1)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _5 := sub(shl(160, 1), 1)
                /// @src 5:31778:31820  "SupplyCollateral(from, dst, asset, amount)"
                let _6 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                /// @src 5:31778:31820  "SupplyCollateral(from, dst, asset, amount)"
                log4(_6, sub(abi_encode_tuple_uint128(_6, expr), _6), 0xfa56f7b24f17183d81894d3ac2ee654e3c26388d17a28dbd9549b8114304e1f4, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:31778:31820  "SupplyCollateral(from, dst, asset, amount)" */ var_from, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _5), and(/** @src 5:31778:31820  "SupplyCollateral(from, dst, asset, amount)" */ var_dst, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _5), and(/** @src 5:31778:31820  "SupplyCollateral(from, dst, asset, amount)" */ var_asset, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _5))
            }
            /// @ast-id 2928 @src 5:23513:24665  "function updateAssetsIn(..."
            function fun_updateAssetsIn(var_account, var_assetInfo_mpos, var_initialUserBalance, var_finalUserBalance)
            {
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _1 := /** @src 1:1927:1931  "1e15" */ sub(shl(128, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)
                /// @src 5:23697:23745  "initialUserBalance == 0 && finalUserBalance != 0"
                let expr := /** @src 5:23697:23720  "initialUserBalance == 0" */ iszero(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:23697:23720  "initialUserBalance == 0" */ var_initialUserBalance, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1))
                /// @src 5:23697:23745  "initialUserBalance == 0 && finalUserBalance != 0"
                let expr_1 := expr
                if expr
                {
                    expr := /** @src 5:23724:23745  "finalUserBalance != 0" */ iszero(iszero(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:23724:23745  "finalUserBalance != 0" */ var_finalUserBalance, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1)))
                }
                /// @src 5:23693:24659  "if (initialUserBalance == 0 && finalUserBalance != 0) {..."
                switch expr
                case 0 {
                    /// @src 5:24179:24227  "initialUserBalance != 0 && finalUserBalance == 0"
                    let expr_2 := /** @src 5:24179:24202  "initialUserBalance != 0" */ iszero(expr_1)
                    /// @src 5:24179:24227  "initialUserBalance != 0 && finalUserBalance == 0"
                    if expr_2
                    {
                        expr_2 := /** @src 5:24206:24227  "finalUserBalance == 0" */ iszero(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:24206:24227  "finalUserBalance == 0" */ var_finalUserBalance, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1))
                    }
                    /// @src 5:24175:24659  "if (initialUserBalance != 0 && finalUserBalance == 0) {..."
                    if expr_2
                    {
                        /// @src 5:24282:24298  "assetInfo.offset"
                        let _2 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_uint8(mload(/** @src 5:24282:24298  "assetInfo.offset" */ var_assetInfo_mpos))
                        /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                        let _3 := and(/** @src 5:24282:24303  "assetInfo.offset < 16" */ _2, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0xff)
                        /// @src 5:24278:24649  "if (assetInfo.offset < 16) {..."
                        switch /** @src 5:24282:24303  "assetInfo.offset < 16" */ lt(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _3, /** @src 5:24301:24303  "16" */ 0x10)
                        case /** @src 5:24278:24649  "if (assetInfo.offset < 16) {..." */ 0 {
                            /// @src 5:24462:24649  "if (assetInfo.offset < 24) {..."
                            if /** @src 5:24466:24487  "assetInfo.offset < 24" */ lt(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _3, /** @src 5:24485:24487  "24" */ 0x18)
                            /// @src 5:24462:24649  "if (assetInfo.offset < 24) {..."
                            {
                                /// @src 5:24596:24634  "~(uint8(1) << (assetInfo.offset - 16))"
                                let expr_3 := cleanup_uint8(not(/** @src 5:24598:24633  "uint8(1) << (assetInfo.offset - 16)" */ shift_left_uint8_uint8(/** @src 5:24604:24605  "1" */ 0x01, /** @src 5:24611:24632  "assetInfo.offset - 16" */ checked_sub_uint8(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _2, /** @src 5:24301:24303  "16" */ 0x10))))
                                /// @src 5:24564:24582  "userBasic[account]"
                                let _4 := mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:24564:24573  "userBasic" */ 0x05, /** @src 5:24564:24582  "userBasic[account]" */ var_account)
                                /// @src 5:24564:24634  "userBasic[account]._reserved &= ~(uint8(1) << (assetInfo.offset - 16))"
                                update_storage_value_offsett_uint8_to_uint8(_4, and(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ extract_from_storage_value_offsett_uint8(sload(/** @src 5:24564:24634  "userBasic[account]._reserved &= ~(uint8(1) << (assetInfo.offset - 16))" */ _4)), expr_3))
                            }
                        }
                        default /// @src 5:24278:24649  "if (assetInfo.offset < 16) {..."
                        {
                            /// @src 5:24409:24441  "~(uint16(1) << assetInfo.offset)"
                            let expr_4 := cleanup_from_storage_uint16(not(/** @src 5:24411:24440  "uint16(1) << assetInfo.offset" */ shift_left_uint16_uint8(/** @src 5:24418:24419  "1" */ 0x01, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_uint8(mload(/** @src 5:24424:24440  "assetInfo.offset" */ var_assetInfo_mpos)))))
                            /// @src 5:24378:24396  "userBasic[account]"
                            let _5 := mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:24378:24387  "userBasic" */ 0x05, /** @src 5:24378:24396  "userBasic[account]" */ var_account)
                            /// @src 5:24378:24441  "userBasic[account].assetsIn &= ~(uint16(1) << assetInfo.offset)"
                            update_storage_value_offsett_uint16_to_uint16(_5, and(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ extract_from_storage_value_offsett_uint16(sload(/** @src 5:24378:24441  "userBasic[account].assetsIn &= ~(uint16(1) << assetInfo.offset)" */ _5)), expr_4))
                        }
                    }
                }
                default /// @src 5:23693:24659  "if (initialUserBalance == 0 && finalUserBalance != 0) {..."
                {
                    /// @src 5:23798:23814  "assetInfo.offset"
                    let _6 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_uint8(mload(/** @src 5:23798:23814  "assetInfo.offset" */ var_assetInfo_mpos))
                    /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                    let _7 := and(/** @src 5:23798:23819  "assetInfo.offset < 16" */ _6, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0xff)
                    /// @src 5:23794:24159  "if (assetInfo.offset < 16) {..."
                    switch /** @src 5:23798:23819  "assetInfo.offset < 16" */ lt(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _7, /** @src 5:23817:23819  "16" */ 0x10)
                    case /** @src 5:23794:24159  "if (assetInfo.offset < 16) {..." */ 0 {
                        /// @src 5:23975:24159  "if (assetInfo.offset < 24) {..."
                        if /** @src 5:23979:24000  "assetInfo.offset < 24" */ lt(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _7, /** @src 5:23998:24000  "24" */ 0x18)
                        /// @src 5:23975:24159  "if (assetInfo.offset < 24) {..."
                        {
                            /// @src 5:24108:24143  "uint8(1) << (assetInfo.offset - 16)"
                            let expr_5 := shift_left_uint8_uint8(/** @src 5:24114:24115  "1" */ 0x01, /** @src 5:24121:24142  "assetInfo.offset - 16" */ checked_sub_uint8(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _6, /** @src 5:23817:23819  "16" */ 0x10))
                            /// @src 5:24075:24093  "userBasic[account]"
                            let _8 := mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:24075:24084  "userBasic" */ 0x05, /** @src 5:24075:24093  "userBasic[account]" */ var_account)
                            /// @src 5:24075:24144  "userBasic[account]._reserved |= (uint8(1) << (assetInfo.offset - 16))"
                            update_storage_value_offsett_uint8_to_uint8(_8, or(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ extract_from_storage_value_offsett_uint8(sload(/** @src 5:24075:24144  "userBasic[account]._reserved |= (uint8(1) << (assetInfo.offset - 16))" */ _8)), expr_5))
                        }
                    }
                    default /// @src 5:23794:24159  "if (assetInfo.offset < 16) {..."
                    {
                        /// @src 5:23924:23953  "uint16(1) << assetInfo.offset"
                        let expr_6 := shift_left_uint16_uint8(/** @src 5:23931:23932  "1" */ 0x01, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_uint8(mload(/** @src 5:23937:23953  "assetInfo.offset" */ var_assetInfo_mpos)))
                        /// @src 5:23892:23910  "userBasic[account]"
                        let _9 := mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:23892:23901  "userBasic" */ 0x05, /** @src 5:23892:23910  "userBasic[account]" */ var_account)
                        /// @src 5:23892:23954  "userBasic[account].assetsIn |= (uint16(1) << assetInfo.offset)"
                        update_storage_value_offsett_uint16_to_uint16(_9, or(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ extract_from_storage_value_offsett_uint16(sload(/** @src 5:23892:23954  "userBasic[account].assetsIn |= (uint16(1) << assetInfo.offset)" */ _9)), expr_6))
                    }
                }
            }
            /// @src 5:33660:34239  "function transferInternal(address operator, address src, address dst, address asset, uint amount) internal nonReentrant {..."
            function fun_transferInternal_inner(var_operator, var_src, var_dst, var_asset, var_amount)
            {
                /// @src 5:33790:33829  "if (isTransferPaused()) revert Paused()"
                if /** @src 3:1636:1642  "x != 0" */ iszero(iszero(/** @src 5:20913:20961  "pauseFlags & (uint8(1) << PAUSE_TRANSFER_OFFSET)" */ and(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ shr(248, sload(/** @src 5:20913:20923  "pauseFlags" */ 0x01)), /** @src 1:1247:1248  "0" */ 2)))
                /// @src 5:33790:33829  "if (isTransferPaused()) revert Paused()"
                {
                    /// @src 5:33821:33829  "Paused()"
                    let _1 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 5:33821:33829  "Paused()"
                    mstore(_1, /** @src 5:45320:45328  "Paused()" */ shl(227, 0x13d0ff59))
                    /// @src 5:33821:33829  "Paused()"
                    revert(_1, 4)
                }
                /// @src 5:33839:33895  "if (!hasPermission(src, operator)) revert Unauthorized()"
                if /** @src 5:33843:33872  "!hasPermission(src, operator)" */ cleanup_bool(iszero(/** @src 5:33844:33872  "hasPermission(src, operator)" */ fun_hasPermission(var_src, var_operator)))
                /// @src 5:33839:33895  "if (!hasPermission(src, operator)) revert Unauthorized()"
                {
                    /// @src 5:33881:33895  "Unauthorized()"
                    let _2 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 5:33881:33895  "Unauthorized()"
                    mstore(_2, /** @src 5:20057:20071  "Unauthorized()" */ shl(232, 8565801))
                    /// @src 5:33881:33895  "Unauthorized()"
                    revert(_2, 4)
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _3 := sub(shl(160, 1), 1)
                /// @src 5:33905:33944  "if (src == dst) revert NoSelfTransfer()"
                if /** @src 5:33909:33919  "src == dst" */ eq(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:33909:33919  "src == dst" */ var_src, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _3), and(/** @src 5:33909:33919  "src == dst" */ var_dst, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _3))
                /// @src 5:33905:33944  "if (src == dst) revert NoSelfTransfer()"
                {
                    /// @src 5:33928:33944  "NoSelfTransfer()"
                    let _4 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 5:33928:33944  "NoSelfTransfer()"
                    mstore(_4, shl(224, 0xe397a99b))
                    revert(_4, 4)
                }
                /// @src 5:33955:34233  "if (asset == baseToken) {..."
                switch /** @src 5:33959:33977  "asset == baseToken" */ eq(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:33959:33977  "asset == baseToken" */ var_asset, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _3), and(/** @src 5:33968:33977  "baseToken" */ loadimmutable("1257"), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _3))
                case /** @src 5:33955:34233  "if (asset == baseToken) {..." */ 0 {
                    /// @src 5:34206:34221  "safe128(amount)"
                    fun_transferCollateral(var_src, var_dst, var_asset, fun_safe128(var_amount))
                    /// @src 5:34163:34222  "return transferCollateral(src, dst, asset, safe128(amount))"
                    leave
                }
                default /// @src 5:33955:34233  "if (asset == baseToken) {..."
                {
                    /// @src 5:33993:34082  "if (amount == type(uint256).max) {..."
                    if /** @src 5:33997:34024  "amount == type(uint256).max" */ eq(var_amount, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ not(0))
                    /// @src 5:33993:34082  "if (amount == type(uint256).max) {..."
                    {
                        /// @src 5:34044:34067  "amount = balanceOf(src)"
                        var_amount := /** @src 5:34053:34067  "balanceOf(src)" */ fun_balanceOf(var_src)
                    }
                    /// @src 5:34125:34131  "amount"
                    fun_transferBase(var_src, var_dst, var_amount)
                    /// @src 5:34095:34132  "return transferBase(src, dst, amount)"
                    leave
                }
            }
            /// @ast-id 3793 @src 5:34355:35989  "function transferBase(address src, address dst, uint256 amount) internal {..."
            function fun_transferBase(var_src, var_dst, var_amount)
            {
                fun_accrueInternal()
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let converted := read_from_storage_reference_type_struct_UserBasic(/** @src 5:34492:34506  "userBasic[src]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:34492:34501  "userBasic" */ 0x05, /** @src 5:34492:34506  "userBasic[src]" */ var_src))
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let converted_1 := read_from_storage_reference_type_struct_UserBasic(/** @src 5:34543:34557  "userBasic[dst]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:34492:34501  "userBasic" */ 0x05, /** @src 5:34543:34557  "userBasic[dst]" */ var_dst))
                /// @src 5:34590:34607  "srcUser.principal"
                let _1 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_from_storage_int104(mload(/** @src 5:34590:34607  "srcUser.principal" */ converted))
                /// @src 5:34639:34656  "dstUser.principal"
                let _2 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_from_storage_int104(mload(/** @src 5:34639:34656  "dstUser.principal" */ converted_1))
                /// @src 5:34686:34712  "presentValue(srcPrincipal)"
                let expr := fun_presentValue(_1)
                /// @src 5:34686:34732  "presentValue(srcPrincipal) - signed256(amount)"
                let expr_1 := checked_sub_int256(expr, /** @src 5:34715:34732  "signed256(amount)" */ fun_signed256(var_amount))
                /// @src 5:34762:34788  "presentValue(dstPrincipal)"
                let expr_2 := fun_presentValue(_2)
                /// @src 5:34762:34808  "presentValue(dstPrincipal) + signed256(amount)"
                let expr_3 := checked_add_int256(expr_2, /** @src 5:34791:34808  "signed256(amount)" */ fun_signed256(var_amount))
                /// @src 5:34843:34869  "principalValue(srcBalance)"
                let expr_4 := fun_principalValue(expr_1)
                /// @src 5:34904:34930  "principalValue(dstBalance)"
                let expr_5 := fun_principalValue(expr_3)
                /// @src 5:34990:35044  "withdrawAndBorrowAmount(srcPrincipal, srcPrincipalNew)"
                let expr_component, expr_3695_component := fun_withdrawAndBorrowAmount(_1, expr_4)
                /// @src 5:35100:35151  "repayAndSupplyAmount(dstPrincipal, dstPrincipalNew)"
                let expr_3704_component, expr_3704_component_1 := fun_repayAndSupplyAmount(_2, expr_5)
                /// @src 5:35250:35315  "totalSupplyBase = totalSupplyBase + supplyAmount - withdrawAmount"
                update_storage_value_offsett_uint104_to_t_uint104(/** @src 5:35268:35283  "totalSupplyBase" */ 0x01, /** @src 5:35268:35315  "totalSupplyBase + supplyAmount - withdrawAmount" */ checked_sub_uint104(/** @src 5:35268:35298  "totalSupplyBase + supplyAmount" */ checked_add_uint104(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ extract_from_storage_value_offsett_uint104(sload(/** @src 5:35268:35283  "totalSupplyBase" */ 0x01)), /** @src 5:35268:35298  "totalSupplyBase + supplyAmount" */ expr_3704_component_1), /** @src 5:35268:35315  "totalSupplyBase + supplyAmount - withdrawAmount" */ expr_component))
                /// @src 5:35325:35387  "totalBorrowBase = totalBorrowBase + borrowAmount - repayAmount"
                update_storage_value_offsett_uint104_to_uint104(/** @src 5:35268:35283  "totalSupplyBase" */ 0x01, /** @src 5:35343:35387  "totalBorrowBase + borrowAmount - repayAmount" */ checked_sub_uint104(/** @src 5:35343:35373  "totalBorrowBase + borrowAmount" */ checked_add_uint104(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ extract_from_storage_value_offset_13t_uint104(sload(/** @src 5:35268:35283  "totalSupplyBase" */ 0x01)), /** @src 5:35343:35373  "totalBorrowBase + borrowAmount" */ expr_3695_component), /** @src 5:35343:35387  "totalBorrowBase + borrowAmount - repayAmount" */ expr_3704_component))
                /// @src 5:35432:35447  "srcPrincipalNew"
                fun_updateBasePrincipal(var_src, converted, expr_4)
                /// @src 5:35492:35507  "dstPrincipalNew"
                fun_updateBasePrincipal(var_dst, converted_1, expr_5)
                /// @src 5:35519:35703  "if (srcBalance < 0) {..."
                if /** @src 5:35523:35537  "srcBalance < 0" */ slt(expr_1, /** @src -1:-1:-1 */ 0)
                /// @src 5:35519:35703  "if (srcBalance < 0) {..."
                {
                    /// @src 5:35565:35576  "-srcBalance"
                    let _3 := negate_int256(expr_1)
                    /// @src 5:35553:35618  "if (uint256(-srcBalance) < baseBorrowMin) revert BorrowTooSmall()"
                    if /** @src 5:35557:35593  "uint256(-srcBalance) < baseBorrowMin" */ lt(_3, /** @src 5:35580:35593  "baseBorrowMin" */ loadimmutable("1325"))
                    /// @src 5:35553:35618  "if (uint256(-srcBalance) < baseBorrowMin) revert BorrowTooSmall()"
                    {
                        /// @src 5:35602:35618  "BorrowTooSmall()"
                        let _4 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                        /// @src 5:35602:35618  "BorrowTooSmall()"
                        mstore(_4, shl(225, 0x7139da23))
                        revert(_4, 4)
                    }
                    /// @src 5:35632:35692  "if (!isBorrowCollateralized(src)) revert NotCollateralized()"
                    if /** @src 5:35636:35664  "!isBorrowCollateralized(src)" */ cleanup_bool(iszero(/** @src 5:35637:35664  "isBorrowCollateralized(src)" */ fun_isBorrowCollateralized(var_src)))
                    /// @src 5:35632:35692  "if (!isBorrowCollateralized(src)) revert NotCollateralized()"
                    {
                        /// @src 5:35673:35692  "NotCollateralized()"
                        let _5 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                        /// @src 5:35673:35692  "NotCollateralized()"
                        mstore(_5, shl(225, 0x0a62fbdb))
                        revert(_5, 4)
                    }
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _6 := sub(shl(104, 1), 1)
                /// @src 5:35713:35845  "if (withdrawAmount > 0) {..."
                if /** @src 5:35717:35735  "withdrawAmount > 0" */ iszero(iszero(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:35717:35735  "withdrawAmount > 0" */ expr_component, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _6)))
                /// @src 5:35713:35845  "if (withdrawAmount > 0) {..."
                {
                    /// @src 5:35782:35833  "presentValueSupply(baseSupplyIndex, withdrawAmount)"
                    let expr_6 := fun_presentValueSupply(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_uint64(sload(/** @src -1:-1:-1 */ 0)), /** @src 5:35782:35833  "presentValueSupply(baseSupplyIndex, withdrawAmount)" */ expr_component)
                    /// @src 5:35756:35834  "Transfer(src, address(0), presentValueSupply(baseSupplyIndex, withdrawAmount))"
                    let _7 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 5:35756:35834  "Transfer(src, address(0), presentValueSupply(baseSupplyIndex, withdrawAmount))"
                    log3(_7, sub(abi_encode_uint256(_7, expr_6), _7), 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:35756:35834  "Transfer(src, address(0), presentValueSupply(baseSupplyIndex, withdrawAmount))" */ var_src, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(shl(160, 1), 1)), /** @src -1:-1:-1 */ 0)
                }
                /// @src 5:35855:35983  "if (supplyAmount > 0) {..."
                if /** @src 5:35859:35875  "supplyAmount > 0" */ iszero(iszero(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:35859:35875  "supplyAmount > 0" */ expr_3704_component_1, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _6)))
                /// @src 5:35855:35983  "if (supplyAmount > 0) {..."
                {
                    /// @src 5:35922:35971  "presentValueSupply(baseSupplyIndex, supplyAmount)"
                    let expr_7 := fun_presentValueSupply(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_uint64(sload(/** @src -1:-1:-1 */ 0)), /** @src 5:35922:35971  "presentValueSupply(baseSupplyIndex, supplyAmount)" */ expr_3704_component_1)
                    /// @src 5:35896:35972  "Transfer(address(0), dst, presentValueSupply(baseSupplyIndex, supplyAmount))"
                    let _8 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 5:35896:35972  "Transfer(address(0), dst, presentValueSupply(baseSupplyIndex, supplyAmount))"
                    log3(_8, sub(abi_encode_uint256(_8, expr_7), _8), 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef, /** @src -1:-1:-1 */ 0, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:35896:35972  "Transfer(address(0), dst, presentValueSupply(baseSupplyIndex, supplyAmount))" */ var_dst, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(shl(160, 1), 1)))
                }
            }
            /// @ast-id 2476 @src 5:18834:19419  "function withdrawAndBorrowAmount(int104 oldPrincipal, int104 newPrincipal) internal pure returns (uint104, uint104) {..."
            function fun_withdrawAndBorrowAmount(var_oldPrincipal, var_newPrincipal) -> var, var_1
            {
                /// @src 5:19077:19104  "newPrincipal > oldPrincipal"
                let _1 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ signextend(12, /** @src 5:19077:19104  "newPrincipal > oldPrincipal" */ var_oldPrincipal)
                let _2 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ signextend(12, /** @src 5:19077:19104  "newPrincipal > oldPrincipal" */ var_newPrincipal)
                /// @src 5:19073:19119  "if (newPrincipal > oldPrincipal) return (0, 0)"
                if /** @src 5:19077:19104  "newPrincipal > oldPrincipal" */ sgt(_2, _1)
                /// @src 5:19073:19119  "if (newPrincipal > oldPrincipal) return (0, 0)"
                {
                    /// @src 5:19106:19119  "return (0, 0)"
                    var := /** @src 5:19114:19115  "0" */ 0x00
                    /// @src 5:19106:19119  "return (0, 0)"
                    var_1 := /** @src 5:19114:19115  "0" */ 0x00
                    /// @src 5:19106:19119  "return (0, 0)"
                    leave
                }
                /// @src 5:19130:19413  "if (newPrincipal >= 0) {..."
                switch /** @src 5:19134:19151  "newPrincipal >= 0" */ iszero(slt(_2, /** @src 5:19150:19151  "0" */ 0x00))
                case /** @src 5:19130:19413  "if (newPrincipal >= 0) {..." */ 0 {
                    /// @src 5:19232:19413  "if (oldPrincipal <= 0) {..."
                    switch /** @src 5:19236:19253  "oldPrincipal <= 0" */ iszero(sgt(_1, /** @src 5:19150:19151  "0" */ 0x00))
                    case /** @src 5:19232:19413  "if (oldPrincipal <= 0) {..." */ 0 {
                        /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                        let _3 := sub(shl(104, 1), 1)
                        let converted := and(_3, /** @src 5:19387:19400  "-newPrincipal" */ negate_int104(var_newPrincipal))
                        /// @src 5:19348:19402  "return (uint104(oldPrincipal), uint104(-newPrincipal))"
                        var := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(_3, /** @src 5:19077:19104  "newPrincipal > oldPrincipal" */ var_oldPrincipal)
                        /// @src 5:19348:19402  "return (uint104(oldPrincipal), uint104(-newPrincipal))"
                        var_1 := converted
                        leave
                    }
                    default /// @src 5:19232:19413  "if (oldPrincipal <= 0) {..."
                    {
                        /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                        let converted_1 := and(sub(shl(104, 1), 1), /** @src 5:19288:19315  "oldPrincipal - newPrincipal" */ checked_sub_int104(var_oldPrincipal, var_newPrincipal))
                        /// @src 5:19269:19317  "return (0, uint104(oldPrincipal - newPrincipal))"
                        var := /** @src 5:19150:19151  "0" */ 0x00
                        /// @src 5:19269:19317  "return (0, uint104(oldPrincipal - newPrincipal))"
                        var_1 := converted_1
                        leave
                    }
                }
                default /// @src 5:19130:19413  "if (newPrincipal >= 0) {..."
                {
                    /// @src 5:19167:19215  "return (uint104(oldPrincipal - newPrincipal), 0)"
                    var := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(sub(shl(104, 1), 1), /** @src 5:19183:19210  "oldPrincipal - newPrincipal" */ checked_sub_int104(var_oldPrincipal, var_newPrincipal))
                    /// @src 5:19167:19215  "return (uint104(oldPrincipal - newPrincipal), 0)"
                    var_1 := /** @src 5:19150:19151  "0" */ 0x00
                    /// @src 5:19167:19215  "return (uint104(oldPrincipal - newPrincipal), 0)"
                    leave
                }
            }
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            function checked_sub_uint128(x, y) -> diff
            {
                let _1 := /** @src 1:1927:1931  "1e15" */ sub(shl(128, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)
                let x_1 := and(x, _1)
                let y_1 := and(y, _1)
                if lt(x_1, y_1) { panic_error_0x11() }
                diff := sub(x_1, y_1)
            }
            /// @ast-id 3890 @src 5:36078:36987  "function transferCollateral(address src, address dst, address asset, uint128 amount) internal {..."
            function fun_transferCollateral(var_src, var_dst, var_asset, var_amount)
            {
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _1 := sub(shl(160, 1), 1)
                let _2 := and(var_src, _1)
                mstore(/** @src -1:-1:-1 */ 0, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _2)
                mstore(0x20, /** @src 5:36206:36220  "userCollateral" */ 0x06)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _3 := /** @src 1:1927:1931  "1e15" */ sub(shl(128, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)
                let value := and(sload(/** @src 5:36206:36232  "userCollateral[src][asset]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ keccak256(/** @src -1:-1:-1 */ 0, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0x40), /** @src 5:36206:36232  "userCollateral[src][asset]" */ var_asset)), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _3)
                let _4 := and(var_dst, _1)
                mstore(/** @src -1:-1:-1 */ 0, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _4)
                mstore(0x20, /** @src 5:36206:36220  "userCollateral" */ 0x06)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let value_1 := and(sload(/** @src 5:36274:36300  "userCollateral[dst][asset]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ keccak256(/** @src -1:-1:-1 */ 0, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0x40), /** @src 5:36274:36300  "userCollateral[dst][asset]" */ var_asset)), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _3)
                /// @src 5:36345:36367  "srcCollateral - amount"
                let expr := checked_sub_uint128(value, var_amount)
                /// @src 5:36404:36426  "dstCollateral + amount"
                let expr_1 := checked_add_uint128(value_1, var_amount)
                /// @src 5:36437:36490  "userCollateral[src][asset].balance = srcCollateralNew"
                update_storage_value_offsett_uint128_to_uint128(/** @src 5:36437:36463  "userCollateral[src][asset]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:36437:36456  "userCollateral[src]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:36206:36220  "userCollateral" */ 0x06, /** @src 5:36437:36456  "userCollateral[src]" */ var_src), /** @src 5:36437:36463  "userCollateral[src][asset]" */ var_asset), /** @src 5:36437:36490  "userCollateral[src][asset].balance = srcCollateralNew" */ expr)
                /// @src 5:36500:36553  "userCollateral[dst][asset].balance = dstCollateralNew"
                update_storage_value_offsett_uint128_to_uint128(/** @src 5:36500:36526  "userCollateral[dst][asset]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:36500:36519  "userCollateral[dst]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:36206:36220  "userCollateral" */ 0x06, /** @src 5:36500:36519  "userCollateral[dst]" */ var_dst), /** @src 5:36500:36526  "userCollateral[dst][asset]" */ var_asset), /** @src 5:36500:36553  "userCollateral[dst][asset].balance = dstCollateralNew" */ expr_1)
                /// @src 5:36593:36621  "getAssetInfoByAddress(asset)"
                let expr_3858_mpos := fun_getAssetInfoByAddress(var_asset)
                /// @src 5:36677:36693  "srcCollateralNew"
                fun_updateAssetsIn(var_src, expr_3858_mpos, value, expr)
                /// @src 5:36750:36766  "dstCollateralNew"
                fun_updateAssetsIn(var_dst, expr_3858_mpos, value_1, expr_1)
                /// @src 5:36861:36921  "if (!isBorrowCollateralized(src)) revert NotCollateralized()"
                if /** @src 5:36865:36893  "!isBorrowCollateralized(src)" */ cleanup_bool(iszero(/** @src 5:36866:36893  "isBorrowCollateralized(src)" */ fun_isBorrowCollateralized(var_src)))
                /// @src 5:36861:36921  "if (!isBorrowCollateralized(src)) revert NotCollateralized()"
                {
                    /// @src 5:36902:36921  "NotCollateralized()"
                    let _5 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(0x40)
                    /// @src 5:36902:36921  "NotCollateralized()"
                    mstore(_5, /** @src 5:35673:35692  "NotCollateralized()" */ shl(225, 0x0a62fbdb))
                    /// @src 5:36902:36921  "NotCollateralized()"
                    revert(_5, 4)
                }
                /// @src 5:36937:36980  "TransferCollateral(src, dst, asset, amount)"
                let _6 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(0x40)
                /// @src 5:36937:36980  "TransferCollateral(src, dst, asset, amount)"
                log4(_6, sub(abi_encode_tuple_uint128(_6, var_amount), _6), 0x29db89d45e1a802b4d55e202984fce9faf1d30aedf86503ff1ea0ed9ebb64201, _2, _4, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:36937:36980  "TransferCollateral(src, dst, asset, amount)" */ var_asset, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1))
            }
            /// @src 5:38330:38857  "function withdrawInternal(address operator, address src, address to, address asset, uint amount) internal nonReentrant {..."
            function fun_withdrawInternal_inner(var_operator, var_src, var_to, var_asset, var_amount)
            {
                /// @src 5:38459:38498  "if (isWithdrawPaused()) revert Paused()"
                if /** @src 3:1636:1642  "x != 0" */ iszero(iszero(/** @src 5:21137:21185  "pauseFlags & (uint8(1) << PAUSE_WITHDRAW_OFFSET)" */ and(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ shr(248, sload(/** @src 5:21137:21147  "pauseFlags" */ 0x01)), /** @src 1:1247:1248  "0" */ 4)))
                /// @src 5:38459:38498  "if (isWithdrawPaused()) revert Paused()"
                {
                    /// @src 5:38490:38498  "Paused()"
                    let _1 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 5:38490:38498  "Paused()"
                    mstore(_1, /** @src 5:45320:45328  "Paused()" */ shl(227, 0x13d0ff59))
                    /// @src 5:38490:38498  "Paused()"
                    revert(_1, /** @src 1:1247:1248  "0" */ 4)
                }
                /// @src 5:38508:38564  "if (!hasPermission(src, operator)) revert Unauthorized()"
                if /** @src 5:38512:38541  "!hasPermission(src, operator)" */ cleanup_bool(iszero(/** @src 5:38513:38541  "hasPermission(src, operator)" */ fun_hasPermission(var_src, var_operator)))
                /// @src 5:38508:38564  "if (!hasPermission(src, operator)) revert Unauthorized()"
                {
                    /// @src 5:38550:38564  "Unauthorized()"
                    let _2 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 5:38550:38564  "Unauthorized()"
                    mstore(_2, /** @src 5:20057:20071  "Unauthorized()" */ shl(232, 8565801))
                    /// @src 5:38550:38564  "Unauthorized()"
                    revert(_2, /** @src 1:1247:1248  "0" */ 4)
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _3 := sub(shl(160, 1), 1)
                /// @src 5:38575:38851  "if (asset == baseToken) {..."
                switch /** @src 5:38579:38597  "asset == baseToken" */ eq(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:38579:38597  "asset == baseToken" */ var_asset, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _3), and(/** @src 5:38588:38597  "baseToken" */ loadimmutable("1257"), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _3))
                case /** @src 5:38575:38851  "if (asset == baseToken) {..." */ 0 {
                    /// @src 5:38824:38839  "safe128(amount)"
                    fun_withdrawCollateral(var_src, var_to, var_asset, fun_safe128(var_amount))
                    /// @src 5:38782:38840  "return withdrawCollateral(src, to, asset, safe128(amount))"
                    leave
                }
                default /// @src 5:38575:38851  "if (asset == baseToken) {..."
                {
                    /// @src 5:38613:38702  "if (amount == type(uint256).max) {..."
                    if /** @src 5:38617:38644  "amount == type(uint256).max" */ eq(var_amount, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ not(0))
                    /// @src 5:38613:38702  "if (amount == type(uint256).max) {..."
                    {
                        /// @src 5:38664:38687  "amount = balanceOf(src)"
                        var_amount := /** @src 5:38673:38687  "balanceOf(src)" */ fun_balanceOf(var_src)
                    }
                    /// @src 5:38744:38750  "amount"
                    fun_withdrawBase(var_src, var_to, var_amount)
                    /// @src 5:38715:38751  "return withdrawBase(src, to, amount)"
                    leave
                }
            }
            /// @ast-id 4142 @src 5:38974:40001  "function withdrawBase(address src, address to, uint256 amount) internal {..."
            function fun_withdrawBase(var_src, var_to, var_amount)
            {
                fun_accrueInternal()
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let converted := read_from_storage_reference_type_struct_UserBasic(/** @src 5:39110:39124  "userBasic[src]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:39110:39119  "userBasic" */ 0x05, /** @src 5:39110:39124  "userBasic[src]" */ var_src))
                /// @src 5:39156:39173  "srcUser.principal"
                let _1 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_from_storage_int104(mload(/** @src 5:39156:39173  "srcUser.principal" */ converted))
                /// @src 5:39203:39229  "presentValue(srcPrincipal)"
                let expr := fun_presentValue(_1)
                /// @src 5:39203:39249  "presentValue(srcPrincipal) - signed256(amount)"
                let expr_1 := checked_sub_int256(expr, /** @src 5:39232:39249  "signed256(amount)" */ fun_signed256(var_amount))
                /// @src 5:39284:39310  "principalValue(srcBalance)"
                let expr_2 := fun_principalValue(expr_1)
                /// @src 5:39370:39424  "withdrawAndBorrowAmount(srcPrincipal, srcPrincipalNew)"
                let expr_4072_component, expr_4072_component_1 := fun_withdrawAndBorrowAmount(_1, expr_2)
                /// @src 5:39435:39468  "totalSupplyBase -= withdrawAmount"
                update_storage_value_offsett_uint104_to_t_uint104(0x01, checked_sub_uint104(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ extract_from_storage_value_offsett_uint104(sload(/** @src 5:39435:39468  "totalSupplyBase -= withdrawAmount" */ 0x01)), expr_4072_component))
                /// @src 5:39478:39509  "totalBorrowBase += borrowAmount"
                update_storage_value_offsett_uint104_to_uint104(/** @src 5:39435:39468  "totalSupplyBase -= withdrawAmount" */ 0x01, /** @src 5:39478:39509  "totalBorrowBase += borrowAmount" */ checked_add_uint104(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ extract_from_storage_value_offset_13t_uint104(sload(/** @src 5:39435:39468  "totalSupplyBase -= withdrawAmount" */ 0x01)), /** @src 5:39478:39509  "totalBorrowBase += borrowAmount" */ expr_4072_component_1))
                /// @src 5:39554:39569  "srcPrincipalNew"
                fun_updateBasePrincipal(var_src, converted, expr_2)
                /// @src 5:39581:39765  "if (srcBalance < 0) {..."
                if /** @src 5:39585:39599  "srcBalance < 0" */ slt(expr_1, /** @src -1:-1:-1 */ 0)
                /// @src 5:39581:39765  "if (srcBalance < 0) {..."
                {
                    /// @src 5:39627:39638  "-srcBalance"
                    let _2 := negate_int256(expr_1)
                    /// @src 5:39615:39680  "if (uint256(-srcBalance) < baseBorrowMin) revert BorrowTooSmall()"
                    if /** @src 5:39619:39655  "uint256(-srcBalance) < baseBorrowMin" */ lt(_2, /** @src 5:39642:39655  "baseBorrowMin" */ loadimmutable("1325"))
                    /// @src 5:39615:39680  "if (uint256(-srcBalance) < baseBorrowMin) revert BorrowTooSmall()"
                    {
                        /// @src 5:39664:39680  "BorrowTooSmall()"
                        let _3 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                        /// @src 5:39664:39680  "BorrowTooSmall()"
                        mstore(_3, /** @src 5:35602:35618  "BorrowTooSmall()" */ shl(225, 0x7139da23))
                        /// @src 5:39664:39680  "BorrowTooSmall()"
                        revert(_3, 4)
                    }
                    /// @src 5:39694:39754  "if (!isBorrowCollateralized(src)) revert NotCollateralized()"
                    if /** @src 5:39698:39726  "!isBorrowCollateralized(src)" */ cleanup_bool(iszero(/** @src 5:39699:39726  "isBorrowCollateralized(src)" */ fun_isBorrowCollateralized(var_src)))
                    /// @src 5:39694:39754  "if (!isBorrowCollateralized(src)) revert NotCollateralized()"
                    {
                        /// @src 5:39735:39754  "NotCollateralized()"
                        let _4 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                        /// @src 5:39735:39754  "NotCollateralized()"
                        mstore(_4, /** @src 5:35673:35692  "NotCollateralized()" */ shl(225, 0x0a62fbdb))
                        /// @src 5:39735:39754  "NotCollateralized()"
                        revert(_4, 4)
                    }
                }
                /// @src 5:39804:39810  "amount"
                fun_doTransferOut(/** @src 5:39789:39798  "baseToken" */ loadimmutable("1257"), /** @src 5:39804:39810  "amount" */ var_to, var_amount)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _5 := sub(shl(160, 1), 1)
                let _6 := and(/** @src 5:39827:39852  "Withdraw(src, to, amount)" */ var_src, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _5)
                /// @src 5:39827:39852  "Withdraw(src, to, amount)"
                let _7 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                /// @src 5:39827:39852  "Withdraw(src, to, amount)"
                log3(_7, sub(abi_encode_uint256(_7, var_amount), _7), 0x9b1bfa7fa9ee420a16e124f794c35ac9f90472acc99140eb2f6447c714cad8eb, _6, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:39827:39852  "Withdraw(src, to, amount)" */ var_to, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _5))
                /// @src 5:39863:39995  "if (withdrawAmount > 0) {..."
                if /** @src 5:39867:39885  "withdrawAmount > 0" */ iszero(iszero(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:39867:39885  "withdrawAmount > 0" */ expr_4072_component, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(shl(104, 1), 1))))
                /// @src 5:39863:39995  "if (withdrawAmount > 0) {..."
                {
                    /// @src 5:39932:39983  "presentValueSupply(baseSupplyIndex, withdrawAmount)"
                    let expr_3 := fun_presentValueSupply(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_uint64(sload(/** @src -1:-1:-1 */ 0)), /** @src 5:39932:39983  "presentValueSupply(baseSupplyIndex, withdrawAmount)" */ expr_4072_component)
                    /// @src 5:39906:39984  "Transfer(src, address(0), presentValueSupply(baseSupplyIndex, withdrawAmount))"
                    let _8 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 5:39906:39984  "Transfer(src, address(0), presentValueSupply(baseSupplyIndex, withdrawAmount))"
                    log3(_8, sub(abi_encode_uint256(_8, expr_3), _8), 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef, _6, /** @src -1:-1:-1 */ 0)
                }
            }
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
            function abi_encode_address_uint256(headStart, value0, value1) -> tail
            {
                tail := add(headStart, 64)
                mstore(headStart, and(value0, sub(shl(160, 1), 1)))
                mstore(add(headStart, 32), value1)
            }
            /// @ast-id 3124 @src 5:27287:28139  "function doTransferOut(address asset, address to, uint amount) internal {..."
            function fun_doTransferOut(var_asset, var_to, var_amount)
            {
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _1 := and(/** @src 5:27369:27393  "IERC20NonStandard(asset)" */ var_asset, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(shl(160, 1), 1))
                /// @src 5:27369:27414  "IERC20NonStandard(asset).transfer(to, amount)"
                if iszero(extcodesize(_1))
                {
                    /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                    revert(0, 0)
                }
                /// @src 5:27369:27414  "IERC20NonStandard(asset).transfer(to, amount)"
                let _2 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                /// @src 5:27369:27414  "IERC20NonStandard(asset).transfer(to, amount)"
                mstore(_2, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ shl(224, 0xa9059cbb))
                /// @src 5:27369:27414  "IERC20NonStandard(asset).transfer(to, amount)"
                let _3 := 0
                let _4 := call(gas(), _1, _3, _2, sub(abi_encode_address_uint256(add(_2, 4), var_to, var_amount), _2), _2, _3)
                if iszero(_4) { revert_forward() }
                if _4 { finalize_allocation(_2, _3) }
                /// @src 5:27424:27436  "bool success"
                let var_success := /** @src 5:27369:27414  "IERC20NonStandard(asset).transfer(to, amount)" */ _3
                /// @src 5:27446:28083  "assembly (\"memory-safe\") {..."
                switch returndatasize()
                case 0 {
                    var_success := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ not(0)
                }
                case /** @src 5:27446:28083  "assembly (\"memory-safe\") {..." */ 32 {
                    returndatacopy(/** @src 5:27369:27414  "IERC20NonStandard(asset).transfer(to, amount)" */ _3, _3, /** @src 5:27446:28083  "assembly (\"memory-safe\") {..." */ 32)
                    var_success := mload(/** @src 5:27369:27414  "IERC20NonStandard(asset).transfer(to, amount)" */ _3)
                }
                default /// @src 5:27446:28083  "assembly (\"memory-safe\") {..."
                {
                    revert(/** @src 5:27369:27414  "IERC20NonStandard(asset).transfer(to, amount)" */ _3, _3)
                }
                /// @src 5:28092:28132  "if (!success) revert TransferOutFailed()"
                if /** @src 5:28096:28104  "!success" */ iszero(var_success)
                /// @src 5:28092:28132  "if (!success) revert TransferOutFailed()"
                {
                    /// @src 5:28113:28132  "TransferOutFailed()"
                    let _5 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 5:28113:28132  "TransferOutFailed()"
                    mstore(_5, shl(224, 0xcefaffeb))
                    revert(_5, /** @src 5:27369:27414  "IERC20NonStandard(asset).transfer(to, amount)" */ 4)
                }
            }
            /// @ast-id 4221 @src 5:40091:40838  "function withdrawCollateral(address src, address to, address asset, uint128 amount) internal {..."
            function fun_withdrawCollateral(var_src, var_to, var_asset, var_amount)
            {
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _1 := sub(shl(160, 1), 1)
                let _2 := and(var_src, _1)
                /// @src -1:-1:-1
                let _3 := 0
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                mstore(/** @src -1:-1:-1 */ _3, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _2)
                mstore(0x20, /** @src 5:40218:40232  "userCollateral" */ 0x06)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _4 := /** @src 1:1927:1931  "1e15" */ sub(shl(128, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)
                let value := and(sload(/** @src 5:40218:40244  "userCollateral[src][asset]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ keccak256(/** @src -1:-1:-1 */ _3, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0x40), /** @src 5:40218:40244  "userCollateral[src][asset]" */ var_asset)), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _4)
                /// @src 5:40289:40311  "srcCollateral - amount"
                let expr := checked_sub_uint128(value, var_amount)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _5 := and(var_asset, _1)
                mstore(/** @src -1:-1:-1 */ _3, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _5)
                mstore(0x20, /** @src 5:40322:40338  "totalsCollateral" */ 0x02)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let dataSlot := keccak256(/** @src -1:-1:-1 */ _3, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0x40)
                /// @src 5:40322:40372  "totalsCollateral[asset].totalSupplyAsset -= amount"
                update_storage_value_offsett_uint128_to_uint128(dataSlot, checked_sub_uint128(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(sload(/** @src 5:40322:40372  "totalsCollateral[asset].totalSupplyAsset -= amount" */ dataSlot), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _4), /** @src 5:40322:40372  "totalsCollateral[asset].totalSupplyAsset -= amount" */ var_amount))
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                mstore(/** @src -1:-1:-1 */ _3, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _2)
                mstore(0x20, /** @src 5:40218:40232  "userCollateral" */ 0x06)
                /// @src 5:40382:40435  "userCollateral[src][asset].balance = srcCollateralNew"
                update_storage_value_offsett_uint128_to_uint128(/** @src 5:40382:40408  "userCollateral[src][asset]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ keccak256(/** @src -1:-1:-1 */ _3, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0x40), /** @src 5:40382:40408  "userCollateral[src][asset]" */ var_asset), /** @src 5:40382:40435  "userCollateral[src][asset].balance = srcCollateralNew" */ expr)
                /// @src 5:40559:40575  "srcCollateralNew"
                fun_updateAssetsIn(var_src, /** @src 5:40475:40503  "getAssetInfoByAddress(asset)" */ fun_getAssetInfoByAddress(var_asset), /** @src 5:40559:40575  "srcCollateralNew" */ value, expr)
                /// @src 5:40670:40730  "if (!isBorrowCollateralized(src)) revert NotCollateralized()"
                if /** @src 5:40674:40702  "!isBorrowCollateralized(src)" */ cleanup_bool(iszero(/** @src 5:40675:40702  "isBorrowCollateralized(src)" */ fun_isBorrowCollateralized(var_src)))
                /// @src 5:40670:40730  "if (!isBorrowCollateralized(src)) revert NotCollateralized()"
                {
                    /// @src 5:40711:40730  "NotCollateralized()"
                    let _6 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(0x40)
                    /// @src 5:40711:40730  "NotCollateralized()"
                    mstore(_6, /** @src 5:35673:35692  "NotCollateralized()" */ shl(225, 0x0a62fbdb))
                    /// @src 5:40711:40730  "NotCollateralized()"
                    revert(_6, 4)
                }
                /// @src 5:40741:40773  "doTransferOut(asset, to, amount)"
                fun_doTransferOut(var_asset, var_to, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:40741:40773  "doTransferOut(asset, to, amount)" */ var_amount, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _4))
                /// @src 5:40789:40831  "WithdrawCollateral(src, to, asset, amount)"
                let _7 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(0x40)
                /// @src 5:40789:40831  "WithdrawCollateral(src, to, asset, amount)"
                log4(_7, sub(abi_encode_tuple_uint128(_7, var_amount), _7), 0xd6d480d5b3068db003533b170d67561494d72e3bf9fa40a266471351ebba9e16, _2, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:40789:40831  "WithdrawCollateral(src, to, asset, amount)" */ var_to, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1), /** @src 5:40789:40831  "WithdrawCollateral(src, to, asset, amount)" */ _5)
            }
            /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
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
                validator_revert_address(value)
                returnValue := value
            }
            function write_to_memory_uint32(memPtr, value)
            {
                mstore(memPtr, and(value, 0xffffffff))
            }
            function read_from_storage_reference_type_struct_LiquidatorPoints(slot) -> value
            {
                let memPtr := mload(64)
                finalize_allocation(memPtr, 128)
                value := memPtr
                let _1 := sload(slot)
                mstore(memPtr, and(_1, 0xffffffff))
                mstore(add(memPtr, 32), and(shr(32, _1), /** @src 1:1927:1931  "1e15" */ sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)))
                mstore(add(memPtr, 64), and(shr(96, _1), /** @src 1:1927:1931  "1e15" */ sub(shl(128, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)))
                mstore(add(memPtr, 96), shr(224, _1))
            }
            function increment_uint32(value) -> ret
            {
                let _1 := 0xffffffff
                let value_1 := and(value, _1)
                if eq(value_1, _1) { panic_error_0x11() }
                ret := add(value_1, 1)
            }
            function copy_struct_to_storage_from_struct_LiquidatorPoints_to_struct_LiquidatorPoints(slot, value)
            {
                let cleaned := and(mload(value), 0xffffffff)
                let _1 := sload(slot)
                sstore(slot, or(and(_1, not(0xffffffff)), cleaned))
                let _2 := and(shl(32, mload(add(value, 32))), sub(shl(96, 1), shl(32, 1)))
                sstore(slot, or(or(and(_1, not(sub(shl(96, 1), 1))), cleaned), _2))
                let _3 := and(shl(96, mload(add(value, 64))), sub(shl(224, 1), shl(96, 1)))
                let _4 := shl(224, 0xffffffff)
                sstore(slot, or(or(_2, or(and(_1, _4), cleaned)), _3))
                sstore(slot, or(or(_3, or(_2, cleaned)), and(shl(224, mload(add(value, 96))), _4)))
            }
            /// @ast-id 4312 @src 5:41092:42061  "function absorb(address absorber, address[] calldata accounts) override external {..."
            function fun_absorb(var_absorber, var_accounts_offset, var_accounts_length)
            {
                /// @src 5:21357:21367  "pauseFlags"
                let _1 := 0x01
                /// @src 5:41183:41220  "if (isAbsorbPaused()) revert Paused()"
                if /** @src 3:1636:1642  "x != 0" */ iszero(iszero(/** @src 5:21357:21403  "pauseFlags & (uint8(1) << PAUSE_ABSORB_OFFSET)" */ and(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ shr(248, sload(/** @src 5:21357:21367  "pauseFlags" */ _1)), /** @src 1:1247:1248  "0" */ 8)))
                /// @src 5:41183:41220  "if (isAbsorbPaused()) revert Paused()"
                {
                    /// @src 5:41212:41220  "Paused()"
                    let _2 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 5:41212:41220  "Paused()"
                    mstore(_2, /** @src 5:45320:45328  "Paused()" */ shl(227, 0x13d0ff59))
                    /// @src 5:41212:41220  "Paused()"
                    revert(_2, 4)
                }
                /// @src 5:41247:41256  "gasleft()"
                let expr := gas()
                /// @src 5:41231:41256  "uint startGas = gasleft()"
                fun_accrueInternal()
                /// @src 5:41297:41307  "uint i = 0"
                let var_i := /** @src 5:41306:41307  "0" */ 0x00
                /// @src 5:41292:41425  "for (uint i = 0; i < accounts.length; ) {..."
                for { }
                /** @src 5:41309:41328  "i < accounts.length" */ lt(var_i, /** @src 5:41313:41328  "accounts.length" */ var_accounts_length)
                /// @src 5:41297:41307  "uint i = 0"
                { }
                {
                    /// @src 5:41371:41382  "accounts[i]"
                    fun_absorbInternal(var_absorber, read_from_calldatat_address(calldata_array_index_access_address_dyn_calldata(var_accounts_offset, var_accounts_length, var_i)))
                    /// @src 5:41409:41412  "i++"
                    var_i := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ add(/** @src 5:41409:41412  "i++" */ var_i, /** @src 5:21357:21367  "pauseFlags" */ _1)
                }
                /// @src 5:41449:41469  "startGas - gasleft()"
                let expr_1 := checked_sub_uint256(expr, /** @src 5:41460:41469  "gasleft()" */ gas())
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let converted := read_from_storage_reference_type_struct_LiquidatorPoints(/** @src 5:41835:41861  "liquidatorPoints[absorber]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:41835:41851  "liquidatorPoints" */ 0x07, /** @src 5:41835:41861  "liquidatorPoints[absorber]" */ var_absorber))
                /// @src 5:41871:41890  "points.numAbsorbs++"
                write_to_memory_uint32(converted, increment_uint32(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_from_storage_uint32(mload(/** @src 5:41871:41890  "points.numAbsorbs++" */ converted))))
                /// @src 5:41922:41945  "safe64(accounts.length)"
                let expr_2 := fun_safe64(/** @src 5:41929:41944  "accounts.length" */ var_accounts_length)
                /// @src 5:41900:41918  "points.numAbsorbed"
                let _3 := add(converted, 32)
                /// @src 5:41900:41945  "points.numAbsorbed += safe64(accounts.length)"
                write_to_memory_uint64(_3, checked_add_uint64(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_uint64(mload(/** @src 5:41900:41945  "points.numAbsorbed += safe64(accounts.length)" */ _3)), expr_2))
                /// @src 5:41977:42009  "safe128(gasUsed * block.basefee)"
                let expr_3 := fun_safe128(/** @src 5:41985:42008  "gasUsed * block.basefee" */ checked_mul_uint256(expr_1, /** @src 5:41995:42008  "block.basefee" */ basefee()))
                /// @src 5:41955:41973  "points.approxSpend"
                let _4 := add(converted, 64)
                /// @src 5:41955:42009  "points.approxSpend += safe128(gasUsed * block.basefee)"
                write_to_memory_uint128(_4, checked_add_uint128(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_from_storage_uint128(mload(/** @src 5:41955:42009  "points.approxSpend += safe128(gasUsed * block.basefee)" */ _4)), expr_3))
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                copy_struct_to_storage_from_struct_LiquidatorPoints_to_struct_LiquidatorPoints(/** @src 5:42019:42045  "liquidatorPoints[absorber]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:41835:41851  "liquidatorPoints" */ 0x07, /** @src 5:42019:42045  "liquidatorPoints[absorber]" */ var_absorber), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ converted)
            }
            function abi_encode_uint128_uint256(headStart, value0, value1) -> tail
            {
                tail := add(headStart, 64)
                mstore(headStart, and(value0, /** @src 1:1927:1931  "1e15" */ sub(shl(128, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)))
                mstore(add(headStart, 32), value1)
            }
            function abi_encode_uint256_uint256(headStart, value0, value1) -> tail
            {
                tail := add(headStart, 64)
                mstore(headStart, value0)
                mstore(add(headStart, 32), value1)
            }
            /// @ast-id 4568 @src 5:42155:44669  "function absorbInternal(address absorber, address account) internal {..."
            function fun_absorbInternal(var_absorber, var_account)
            {
                /// @src 5:42233:42287  "if (!isLiquidatable(account)) revert NotLiquidatable()"
                if /** @src 5:42237:42261  "!isLiquidatable(account)" */ cleanup_bool(iszero(/** @src 5:42238:42261  "isLiquidatable(account)" */ fun_isLiquidatable(var_account)))
                /// @src 5:42233:42287  "if (!isLiquidatable(account)) revert NotLiquidatable()"
                {
                    /// @src 5:42270:42287  "NotLiquidatable()"
                    let _1 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 5:42270:42287  "NotLiquidatable()"
                    mstore(_1, shl(225, 0x6ef5bcdd))
                    revert(_1, 4)
                }
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let converted := read_from_storage_reference_type_struct_UserBasic(/** @src 5:42329:42347  "userBasic[account]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:42329:42338  "userBasic" */ 0x05, /** @src 5:42329:42347  "userBasic[account]" */ var_account))
                /// @src 5:42379:42400  "accountUser.principal"
                let _2 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_from_storage_int104(mload(/** @src 5:42379:42400  "accountUser.principal" */ converted))
                /// @src 5:42430:42456  "presentValue(oldPrincipal)"
                let expr := fun_presentValue(_2)
                /// @src 5:42484:42504  "accountUser.assetsIn"
                let _3 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_from_storage_uint16(mload(/** @src 5:42484:42504  "accountUser.assetsIn" */ add(converted, 96)))
                /// @src 5:42532:42553  "accountUser._reserved"
                let _4 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_uint8(mload(/** @src 5:42532:42553  "accountUser._reserved" */ add(converted, 128)))
                /// @src 5:42584:42612  "getPrice(baseTokenPriceFeed)"
                let expr_1 := fun_getPrice(/** @src 5:42593:42611  "baseTokenPriceFeed" */ loadimmutable("1261"))
                /// @src 5:42622:42644  "uint256 deltaValue = 0"
                let var_deltaValue := /** @src -1:-1:-1 */ 0
                /// @src 5:42660:42671  "uint8 i = 0"
                let var_i := /** @src -1:-1:-1 */ var_deltaValue
                /// @src 5:42655:43388  "for (uint8 i = 0; i < numAssets; ) {..."
                for { }
                /** @src 5:42673:42686  "i < numAssets" */ lt(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:42673:42686  "i < numAssets" */ var_i, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0xff), and(/** @src 5:42677:42686  "numAssets" */ loadimmutable("1337"), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0xff))
                /// @src 5:42660:42671  "uint8 i = 0"
                { }
                {
                    /// @src 5:42704:43347  "if (isInAsset(assetsIn, i, _reserved)) {..."
                    if /** @src 5:42708:42741  "isInAsset(assetsIn, i, _reserved)" */ fun_isInAsset(_3, var_i, _4)
                    /// @src 5:42704:43347  "if (isInAsset(assetsIn, i, _reserved)) {..."
                    {
                        /// @src 5:42790:42805  "getAssetInfo(i)"
                        let expr_mpos := fun_getAssetInfo(var_i)
                        /// @src 5:42839:42854  "assetInfo.asset"
                        let _5 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_address(mload(/** @src 5:42839:42854  "assetInfo.asset" */ add(expr_mpos, 32)))
                        /// @src 5:42894:42932  "userCollateral[account][asset].balance"
                        let _6 := read_from_storage_split_offset_uint128(/** @src 5:42894:42924  "userCollateral[account][asset]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:42894:42917  "userCollateral[account]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:42894:42908  "userCollateral" */ 0x06, /** @src 5:42894:42917  "userCollateral[account]" */ var_account), /** @src 5:42894:42924  "userCollateral[account][asset]" */ _5))
                        /// @src 5:42950:42992  "userCollateral[account][asset].balance = 0"
                        update_storage_value_offsett_uint128_to_uint128(/** @src 5:42950:42980  "userCollateral[account][asset]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:42950:42973  "userCollateral[account]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:42894:42908  "userCollateral" */ 0x06, /** @src 5:42950:42973  "userCollateral[account]" */ var_account), /** @src 5:42950:42980  "userCollateral[account][asset]" */ _5), /** @src -1:-1:-1 */ 0)
                        /// @src 5:43010:43033  "totalsCollateral[asset]"
                        let _7 := mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:43010:43026  "totalsCollateral" */ 0x02, /** @src 5:43010:43033  "totalsCollateral[asset]" */ _5)
                        /// @src 5:43010:43065  "totalsCollateral[asset].totalSupplyAsset -= seizeAmount"
                        update_storage_value_offsett_uint128_to_uint128(_7, checked_sub_uint128(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_from_storage_uint128(sload(/** @src 5:43010:43065  "totalsCollateral[asset].totalSupplyAsset -= seizeAmount" */ _7)), _6))
                        /// @src 5:43122:43151  "getPrice(assetInfo.priceFeed)"
                        let expr_2 := fun_getPrice(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_address(mload(/** @src 5:43131:43150  "assetInfo.priceFeed" */ add(expr_mpos, 64))))
                        /// @src 5:43100:43169  "mulPrice(seizeAmount, getPrice(assetInfo.priceFeed), assetInfo.scale)"
                        let expr_3 := fun_mulPrice(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:43100:43169  "mulPrice(seizeAmount, getPrice(assetInfo.priceFeed), assetInfo.scale)" */ _6, /** @src 1:1927:1931  "1e15" */ sub(shl(128, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)), /** @src 5:43100:43169  "mulPrice(seizeAmount, getPrice(assetInfo.priceFeed), assetInfo.scale)" */ expr_2, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_uint64(mload(/** @src 5:43153:43168  "assetInfo.scale" */ add(expr_mpos, /** @src 5:42484:42504  "accountUser.assetsIn" */ 96))))
                        /// @src 5:43187:43246  "deltaValue += mulFactor(value, assetInfo.liquidationFactor)"
                        var_deltaValue := checked_add_uint256(var_deltaValue, /** @src 5:43201:43246  "mulFactor(value, assetInfo.liquidationFactor)" */ fun_mulFactor(expr_3, cleanup_uint64(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_uint64(mload(/** @src 5:43218:43245  "assetInfo.liquidationFactor" */ add(expr_mpos, 192))))))
                        /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                        let _8 := sub(shl(160, 1), 1)
                        /// @src 5:43270:43332  "AbsorbCollateral(absorber, account, asset, seizeAmount, value)"
                        let _9 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(/** @src 5:43131:43150  "assetInfo.priceFeed" */ 64)
                        /// @src 5:43270:43332  "AbsorbCollateral(absorber, account, asset, seizeAmount, value)"
                        log4(_9, sub(abi_encode_uint128_uint256(_9, _6, expr_3), _9), 0x9850ab1af75177e4a9201c65a2cf7976d5d28e40ef63494b44366f86b2f9412e, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:43270:43332  "AbsorbCollateral(absorber, account, asset, seizeAmount, value)" */ var_absorber, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _8), and(/** @src 5:43270:43332  "AbsorbCollateral(absorber, account, asset, seizeAmount, value)" */ var_account, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _8), and(/** @src 5:43270:43332  "AbsorbCollateral(absorber, account, asset, seizeAmount, value)" */ _5, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _8))
                    }
                    /// @src 5:43372:43375  "i++"
                    var_i := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(add(/** @src 5:43372:43375  "i++" */ var_i, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 0xff)
                }
                /// @src 5:43453:43470  "uint64(baseScale)"
                let expr_4 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:43460:43469  "baseScale" */ loadimmutable("1305"), /** @src 1:1927:1931  "1e15" */ sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1))
                /// @src 5:43481:43537  "int256 newBalance = oldBalance + signed256(deltaBalance)"
                let var_newBalance := /** @src 5:43501:43537  "oldBalance + signed256(deltaBalance)" */ checked_add_int256(expr, /** @src 5:43514:43537  "signed256(deltaBalance)" */ fun_signed256(/** @src 5:22722:22741  "n * toScale / price" */ checked_div_uint256(/** @src 5:22722:22733  "n * toScale" */ checked_mul_uint256(/** @src 5:43421:43471  "divPrice(deltaValue, basePrice, uint64(baseScale))" */ var_deltaValue, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ expr_4), /** @src 5:43421:43471  "divPrice(deltaValue, basePrice, uint64(baseScale))" */ expr_1)))
                /// @src 5:43629:43688  "if (newBalance < 0) {..."
                if /** @src 5:43633:43647  "newBalance < 0" */ slt(var_newBalance, /** @src -1:-1:-1 */ 0)
                /// @src 5:43629:43688  "if (newBalance < 0) {..."
                {
                    /// @src 5:43663:43677  "newBalance = 0"
                    var_newBalance := /** @src -1:-1:-1 */ 0
                }
                /// @src 5:43720:43746  "principalValue(newBalance)"
                let expr_5 := fun_principalValue(var_newBalance)
                /// @src 5:43798:43810  "newPrincipal"
                fun_updateBasePrincipal(var_account, converted, expr_5)
                /// @src 5:43848:43879  "userBasic[account].assetsIn = 0"
                update_storage_value_offsett_uint16_to_uint16(/** @src 5:43848:43866  "userBasic[account]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:42329:42338  "userBasic" */ 0x05, /** @src 5:43848:43866  "userBasic[account]" */ var_account), /** @src -1:-1:-1 */ 0)
                /// @src 5:43889:43921  "userBasic[account]._reserved = 0"
                update_storage_value_offsett_uint8_to_uint8(/** @src 5:43889:43907  "userBasic[account]" */ mapping_index_access_mapping_address_mapping_address_struct_UserCollateral_storage_of_address(/** @src 5:42329:42338  "userBasic" */ 0x05, /** @src 5:43889:43907  "userBasic[account]" */ var_account), /** @src -1:-1:-1 */ 0)
                /// @src 5:43978:44026  "repayAndSupplyAmount(oldPrincipal, newPrincipal)"
                let expr_4512_component, expr_4512_component_1 := fun_repayAndSupplyAmount(_2, expr_5)
                /// @src 5:44200:44231  "totalSupplyBase += supplyAmount"
                update_storage_value_offsett_uint104_to_t_uint104(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1, /** @src 5:44200:44231  "totalSupplyBase += supplyAmount" */ checked_add_uint104(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ extract_from_storage_value_offsett_uint104(sload(1)), /** @src 5:44200:44231  "totalSupplyBase += supplyAmount" */ expr_4512_component_1))
                /// @src 5:44241:44271  "totalBorrowBase -= repayAmount"
                update_storage_value_offsett_uint104_to_uint104(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1, /** @src 5:44241:44271  "totalBorrowBase -= repayAmount" */ checked_sub_uint104(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ extract_from_storage_value_offset_13t_uint104(sload(1)), /** @src 5:44241:44271  "totalBorrowBase -= repayAmount" */ expr_4512_component))
                /// @src 5:44304:44340  "unsigned256(newBalance - oldBalance)"
                let expr_6 := fun_unsigned256(/** @src 5:44316:44339  "newBalance - oldBalance" */ checked_sub_int256(var_newBalance, expr))
                /// @src 5:44379:44430  "mulPrice(basePaidOut, basePrice, uint64(baseScale))"
                let expr_7 := fun_mulPrice(expr_6, expr_1, expr_4)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _10 := sub(shl(160, 1), 1)
                let _11 := and(/** @src 5:44445:44507  "AbsorbDebt(absorber, account, basePaidOut, valueOfBasePaidOut)" */ var_account, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _10)
                /// @src 5:44445:44507  "AbsorbDebt(absorber, account, basePaidOut, valueOfBasePaidOut)"
                let _12 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                /// @src 5:44445:44507  "AbsorbDebt(absorber, account, basePaidOut, valueOfBasePaidOut)"
                log3(_12, sub(abi_encode_uint256_uint256(_12, expr_6, expr_7), _12), 0x1547a878dc89ad3c367b6338b4be6a65a5dd74fb77ae044da1e8747ef1f4f62f, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:44445:44507  "AbsorbDebt(absorber, account, basePaidOut, valueOfBasePaidOut)" */ var_absorber, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _10), /** @src 5:44445:44507  "AbsorbDebt(absorber, account, basePaidOut, valueOfBasePaidOut)" */ _11)
                /// @src 5:44518:44663  "if (newPrincipal > 0) {..."
                if /** @src 5:44522:44538  "newPrincipal > 0" */ sgt(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ signextend(12, /** @src 5:44522:44538  "newPrincipal > 0" */ expr_5), /** @src -1:-1:-1 */ 0)
                /// @src 5:44518:44663  "if (newPrincipal > 0) {..."
                {
                    /// @src 5:44608:44623  "baseSupplyIndex"
                    let _13 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleanup_uint64(sload(/** @src -1:-1:-1 */ 0))
                    /// @src 5:44589:44651  "presentValueSupply(baseSupplyIndex, unsigned104(newPrincipal))"
                    let expr_8 := fun_presentValueSupply(_13, /** @src 5:44625:44650  "unsigned104(newPrincipal)" */ fun_unsigned104(expr_5))
                    /// @src 5:44559:44652  "Transfer(address(0), account, presentValueSupply(baseSupplyIndex, unsigned104(newPrincipal)))"
                    let _14 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 5:44559:44652  "Transfer(address(0), account, presentValueSupply(baseSupplyIndex, unsigned104(newPrincipal)))"
                    log3(_14, sub(abi_encode_uint256(_14, expr_8), _14), 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef, /** @src -1:-1:-1 */ 0, /** @src 5:44559:44652  "Transfer(address(0), account, presentValueSupply(baseSupplyIndex, unsigned104(newPrincipal)))" */ _11)
                }
            }
            /// @ast-id 1082 @src 3:1177:1318  "function unsigned104(int104 n) internal pure returns (uint104) {..."
            function fun_unsigned104(var_n) -> var
            {
                /// @src 3:1250:1284  "if (n < 0) revert NegativeNumber()"
                if /** @src 3:1254:1259  "n < 0" */ slt(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ signextend(12, /** @src 3:1254:1259  "n < 0" */ var_n), /** @src 3:1258:1259  "0" */ 0x00)
                /// @src 3:1250:1284  "if (n < 0) revert NegativeNumber()"
                {
                    /// @src 3:1268:1284  "NegativeNumber()"
                    let _1 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 3:1268:1284  "NegativeNumber()"
                    mstore(_1, shl(225, 0x363b64b7))
                    revert(_1, 4)
                }
                /// @src 3:1294:1311  "return uint104(n)"
                var := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(sub(shl(104, 1), 1), /** @src 3:1254:1259  "n < 0" */ var_n)
            }
            /// @ast-id 1102 @src 3:1324:1465  "function unsigned256(int256 n) internal pure returns (uint256) {..."
            function fun_unsigned256(var_n) -> var
            {
                /// @src 3:1397:1431  "if (n < 0) revert NegativeNumber()"
                if /** @src 3:1401:1406  "n < 0" */ slt(var_n, /** @src 3:1405:1406  "0" */ 0x00)
                /// @src 3:1397:1431  "if (n < 0) revert NegativeNumber()"
                {
                    /// @src 3:1415:1431  "NegativeNumber()"
                    let _1 := /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ mload(64)
                    /// @src 3:1415:1431  "NegativeNumber()"
                    mstore(_1, /** @src 3:1268:1284  "NegativeNumber()" */ shl(225, 0x363b64b7))
                    /// @src 3:1415:1431  "NegativeNumber()"
                    revert(_1, 4)
                }
                /// @src 3:1441:1458  "return uint256(n)"
                var := var_n
            }
            /// @ast-id 4719 @src 5:46645:47622  "function quoteCollateral(address asset, uint baseAmount) override public view returns (uint) {..."
            function fun_quoteCollateral(var_asset, var_baseAmount) -> var
            {
                /// @src 5:46777:46805  "getAssetInfoByAddress(asset)"
                let expr_4673_mpos := fun_getAssetInfoByAddress(var_asset)
                /// @src 5:46836:46865  "getPrice(assetInfo.priceFeed)"
                let expr := fun_getPrice(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(mload(/** @src 5:46845:46864  "assetInfo.priceFeed" */ add(expr_4673_mpos, 64)), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(shl(160, 1), 1)))
                let _1 := /** @src 1:1927:1931  "1e15" */ sub(shl(64, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 1), 1)
                let _2 := and(mload(/** @src 5:47136:47163  "assetInfo.liquidationFactor" */ add(expr_4673_mpos, 192)), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1)
                /// @src 1:2135:2139  "1e18"
                let _3 := 0x0de0b6b3a7640000
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                if lt(/** @src 1:2135:2139  "1e18" */ _3, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _2) { panic_error_0x11() }
                /// @src 5:47088:47164  "mulFactor(storeFrontPriceFactor, FACTOR_SCALE - assetInfo.liquidationFactor)"
                let _4 := /** @src 1:2135:2139  "1e18" */ div(/** @src 5:21770:21780  "n * factor" */ checked_mul_uint256(/** @src 5:47098:47119  "storeFrontPriceFactor" */ loadimmutable("1301"), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(sub(/** @src 1:2135:2139  "1e18" */ _3, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _2), _1)), /** @src 1:2135:2139  "1e18" */ _3)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                if lt(/** @src 1:2135:2139  "1e18" */ _3, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _4) { panic_error_0x11() }
                /// @src 5:47205:47257  "mulFactor(assetPrice, FACTOR_SCALE - discountFactor)"
                let expr_1 := /** @src 1:2135:2139  "1e18" */ div(/** @src 5:21770:21780  "n * factor" */ checked_mul_uint256(/** @src 5:47205:47257  "mulFactor(assetPrice, FACTOR_SCALE - discountFactor)" */ expr, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ sub(/** @src 1:2135:2139  "1e18" */ _3, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _4)), /** @src 1:2135:2139  "1e18" */ _3)
                /// @src 5:47540:47562  "basePrice * baseAmount"
                let expr_2 := checked_mul_uint256(/** @src 5:47287:47315  "getPrice(baseTokenPriceFeed)" */ fun_getPrice(/** @src 5:47296:47314  "baseTokenPriceFeed" */ loadimmutable("1261")), /** @src 5:47540:47562  "basePrice * baseAmount" */ var_baseAmount)
                /// @src 5:47540:47580  "basePrice * baseAmount * assetInfo.scale"
                let _5 := checked_mul_uint256(expr_2, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(mload(/** @src 5:47565:47580  "assetInfo.scale" */ add(expr_4673_mpos, 96)), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1))
                /// @src 1:2135:2139  "1e18"
                if iszero(expr_1) { panic_error_0x12() }
                /// @src 5:47533:47615  "return basePrice * baseAmount * assetInfo.scale / assetPriceDiscounted / baseScale"
                var := /** @src 5:47540:47615  "basePrice * baseAmount * assetInfo.scale / assetPriceDiscounted / baseScale" */ checked_div_uint256(/** @src 1:2135:2139  "1e18" */ div(_5, expr_1), /** @src 5:47606:47615  "baseScale" */ loadimmutable("1305"))
            }
            /// @ast-id 4876 @src 5:50128:50462  "function balanceOf(address account) override public view returns (uint256) {..."
            function fun_balanceOf(var_account) -> var
            {
                /// @src 5:50266:50282  "getNowInternal()"
                let expr := fun_getNowInternal()
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _1 := 0xffffffffff
                /// @src 5:50243:50301  "accruedInterestIndices(getNowInternal() - lastAccrualTime)"
                let expr_4854_component, expr_4854_component_1 := fun_accruedInterestIndices(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:50266:50300  "getNowInternal() - lastAccrualTime" */ checked_sub_uint40(expr, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(shr(208, sload(/** @src 5:50285:50300  "lastAccrualTime" */ 0x01)), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1)), _1))
                mstore(/** @src -1:-1:-1 */ 0, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(var_account, sub(shl(160, 1), 1)))
                mstore(0x20, /** @src 5:50330:50339  "userBasic" */ 0x05)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let cleaned := signextend(12, sload(keccak256(/** @src -1:-1:-1 */ 0, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0x40)))
                /// @src 5:50375:50455  "principal > 0 ? presentValueSupply(baseSupplyIndex_, unsigned104(principal)) : 0"
                let expr_1 := /** @src -1:-1:-1 */ 0
                /// @src 5:50375:50455  "principal > 0 ? presentValueSupply(baseSupplyIndex_, unsigned104(principal)) : 0"
                switch /** @src 5:50375:50388  "principal > 0" */ sgt(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleaned, /** @src -1:-1:-1 */ expr_1)
                case /** @src 5:50375:50455  "principal > 0 ? presentValueSupply(baseSupplyIndex_, unsigned104(principal)) : 0" */ 0 {
                    expr_1 := /** @src -1:-1:-1 */ expr_1
                }
                default /// @src 5:50375:50455  "principal > 0 ? presentValueSupply(baseSupplyIndex_, unsigned104(principal)) : 0"
                {
                    expr_1 := /** @src 5:50391:50451  "presentValueSupply(baseSupplyIndex_, unsigned104(principal))" */ fun_presentValueSupply(expr_4854_component, /** @src 5:50428:50450  "unsigned104(principal)" */ fun_unsigned104(cleaned))
                }
                /// @src 5:50368:50455  "return principal > 0 ? presentValueSupply(baseSupplyIndex_, unsigned104(principal)) : 0"
                var := expr_1
            }
            /// @ast-id 4915 @src 5:50761:51102  "function borrowBalanceOf(address account) override public view returns (uint256) {..."
            function fun_borrowBalanceOf(var_account) -> var
            {
                /// @src 5:50905:50921  "getNowInternal()"
                let expr := fun_getNowInternal()
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let _1 := 0xffffffffff
                /// @src 5:50882:50940  "accruedInterestIndices(getNowInternal() - lastAccrualTime)"
                let expr_4892_component, expr_component := fun_accruedInterestIndices(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(/** @src 5:50905:50939  "getNowInternal() - lastAccrualTime" */ checked_sub_uint40(expr, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(shr(208, sload(/** @src 5:50924:50939  "lastAccrualTime" */ 0x01)), /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ _1)), _1))
                mstore(/** @src -1:-1:-1 */ 0, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ and(var_account, sub(shl(160, 1), 1)))
                mstore(0x20, /** @src 5:50969:50978  "userBasic" */ 0x05)
                /// @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..."
                let cleaned := signextend(12, sload(keccak256(/** @src -1:-1:-1 */ 0, /** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ 0x40)))
                /// @src 5:51014:51095  "principal < 0 ? presentValueBorrow(baseBorrowIndex_, unsigned104(-principal)) : 0"
                let expr_1 := /** @src -1:-1:-1 */ 0
                /// @src 5:51014:51095  "principal < 0 ? presentValueBorrow(baseBorrowIndex_, unsigned104(-principal)) : 0"
                switch /** @src 5:51014:51027  "principal < 0" */ slt(/** @src 5:436:51622  "contract CometWithExtendedAssetList is CometMainInterface {..." */ cleaned, /** @src -1:-1:-1 */ expr_1)
                case /** @src 5:51014:51095  "principal < 0 ? presentValueBorrow(baseBorrowIndex_, unsigned104(-principal)) : 0" */ 0 {
                    expr_1 := /** @src -1:-1:-1 */ expr_1
                }
                default /// @src 5:51014:51095  "principal < 0 ? presentValueBorrow(baseBorrowIndex_, unsigned104(-principal)) : 0"
                {
                    expr_1 := /** @src 5:51030:51091  "presentValueBorrow(baseBorrowIndex_, unsigned104(-principal))" */ fun_presentValueSupply(expr_component, /** @src 5:51067:51090  "unsigned104(-principal)" */ fun_unsigned104(/** @src 5:51079:51089  "-principal" */ negate_int104(cleaned)))
                }
                /// @src 5:51007:51095  "return principal < 0 ? presentValueBorrow(baseBorrowIndex_, unsigned104(-principal)) : 0"
                var := expr_1
            }
            /// @ast-id 4925 @src 5:51202:51620  "fallback() external payable {..."
            function fun()
            {
                /// @src 5:51286:51614  "assembly {..."
                let _1 := 0
                calldatacopy(_1, _1, calldatasize())
                let usr$result := delegatecall(gas(), /** @src 5:51259:51276  "extensionDelegate" */ loadimmutable("1265"), /** @src 5:51286:51614  "assembly {..." */ _1, calldatasize(), _1, _1)
                returndatacopy(_1, _1, returndatasize())
                switch usr$result
                case 0 { revert(_1, returndatasize()) }
                default { return(_1, returndatasize()) }
            }
        }
        data ".metadata" hex"a2646970667358221220b1cfb58988995688aecfece4ee22db00750a883d592dfdbf24f44419fa666b5264736f6c634300080f0033"
    }
}
