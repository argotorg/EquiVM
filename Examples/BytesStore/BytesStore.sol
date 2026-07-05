// SPDX-License-Identifier: MIT
// Runtime bytecode can be generated with:
//   solc --optimize --optimize-runs 200 --evm-version shanghai --bin-runtime \
//     Examples/BytesStore/BytesStore.sol
// optimizer ON.
pragma solidity ^0.8.20;

contract BytesStore {
    struct Packet {
        bytes data;
        uint256 tag;
    }

    bytes private current;          // slot 0: Solidity short/long bytes layout
    bytes[] private chunks;         // slot 1: dynamic array of dynamic bytes
    Packet private packet;          // slot 2: bytes field plus scalar field
    mapping(uint256 => bytes) private mapped; // slot 4: mapping to dynamic bytes

    function set(bytes calldata value) external returns (uint256 currentBytes) {
        bytes memory copy = value;
        current = copy;
        currentBytes = copy.length;
    }

    function setByte(uint256 index, uint8 value) external returns (uint8 written) {
        current[index] = bytes1(value);
        written = uint8(current[index]);
    }

    function clearCurrent() external returns (uint256 oldBytes) {
        bytes memory copy = current;
        oldBytes = copy.length;
        delete current;
    }

    function currentLength() external view returns (uint256) {
        return current.length;
    }

    function pushChunk(bytes calldata value) external returns (uint256 chunkCount) {
        chunks.push(value);
        chunkCount = chunks.length;
    }

    function setChunk(uint256 chunkIndex, bytes calldata value) external returns (uint256 chunkBytes) {
        chunks[chunkIndex] = value;
        chunkBytes = chunks[chunkIndex].length;
    }

    function setChunkByte(uint256 chunkIndex, uint256 byteIndex, uint8 value)
        external
        returns (uint8 written)
    {
        chunks[chunkIndex][byteIndex] = bytes1(value);
        written = uint8(chunks[chunkIndex][byteIndex]);
    }

    function chunkLength(uint256 chunkIndex) external view returns (uint256) {
        return chunks[chunkIndex].length;
    }

    function setPacket(bytes calldata value, uint256 tag) external returns (uint256 packetBytes) {
        packet.data = value;
        packet.tag = tag;
        packetBytes = packet.data.length;
    }

    function setPacketByte(uint256 byteIndex, uint8 value) external returns (uint8 written) {
        packet.data[byteIndex] = bytes1(value);
        written = uint8(packet.data[byteIndex]);
    }

    function packetLength() external view returns (uint256) {
        return packet.data.length;
    }

    function packetTag() external view returns (uint256) {
        return packet.tag;
    }

    function setMapped(uint256 key, bytes calldata value) external returns (uint256 mappedBytes) {
        mapped[key] = value;
        mappedBytes = mapped[key].length;
    }

    function setMappedByte(uint256 key, uint256 byteIndex, uint8 value) external returns (uint8 written) {
        mapped[key][byteIndex] = bytes1(value);
        written = uint8(mapped[key][byteIndex]);
    }

    function mappedLength(uint256 key) external view returns (uint256) {
        return mapped[key].length;
    }
}
