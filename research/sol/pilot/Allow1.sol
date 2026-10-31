// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;
/// gdp: law transferFrom never mints: totalSupply == old(totalSupply)
contract Allow1 {
    mapping(address => uint256) balances;
    mapping(address => uint256) allow;
    uint256 totalSupply;
    function transferFrom(address from, address to, uint256 value) external {
        uint256 a = allow[from];
        if (a != type(uint256).max) { require(a >= value); unchecked { allow[from] = a - value; } }
        uint256 b = balances[from];
        require(b >= value);
        unchecked { balances[from] = b - value; balances[to] += value; }
    }
}
