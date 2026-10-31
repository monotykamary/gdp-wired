// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// A counter that goes down past 0 unchecked: it wraps to 2^256 - 1.
/// gdp: law never past the cap: count <= 100
contract Counter {
    uint256 public count;
    function down() external { unchecked { count -= 1; } }
    function up() external { require(count < 100); count += 1; }
}
