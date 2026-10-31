// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// A minimal ledger: checked arithmetic, a transfer between two accounts in one step.
/// gdp: law the balances sum to the supply: sum(balances) == totalSupply
contract Token {
    mapping(address => uint256) public balances;
    uint256 public totalSupply;
    address public owner;

    constructor() { owner = msg.sender; }

    function mint(address to, uint256 amount) external {
        require(msg.sender == owner, "not the owner");
        require(to != address(0), "zero");
        totalSupply += amount;
        balances[to] += amount;
    }

    /// gdp: law transfer never mints: totalSupply == old(totalSupply)
    function transfer(address to, uint256 amount) external returns (bool) {
        require(to != address(0), "zero");
        uint256 b = balances[msg.sender];
        require(b >= amount, "balance");
        unchecked { balances[msg.sender] = b - amount; }
        balances[to] += amount;
        return true;
    }

    function burn(uint256 amount) external {
        uint256 b = balances[msg.sender];
        require(b >= amount, "balance");
        unchecked { balances[msg.sender] = b - amount; totalSupply -= amount; }
    }
}
