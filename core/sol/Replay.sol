// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// The re-entrant runs of core/extract-sol.ts replayed on the code: every address a run names is an Agent (its code set
// there), and one Director holds the run's script. A call of the script is made by its Agent; a call into an Agent (the
// contract sending it a value) runs the script's next calls from inside it, up to a return (the Agent's call returns, or
// reverts). The Director records whether each call of the script succeeded.
interface IDirector { function onCall() external returns (bool); }

contract Agent {
    address constant DIRECTOR = address(uint160(0xD1EC70));
    function act(address t, uint256 v, bytes calldata d) external returns (bool ok) {
        require(msg.sender == DIRECTOR, "agent: the director only");
        (ok, ) = t.call{value: v}(d);
    }
    receive() external payable { if (!IDirector(DIRECTOR).onCall()) revert("agent: the callee reverts"); }
    fallback() external payable { if (!IDirector(DIRECTOR).onCall()) revert("agent: the callee reverts"); }
}

contract Director {
    uint8[] kinds;
    address[] froms;
    uint256[] values;
    bool[] rets;
    bytes[] datas;
    uint256 at;
    address target;
    bool[] public oks;

    // One transaction of the run: its first call, and inside it every call and return the script holds.
    function run(address t, uint8[] calldata k, address[] calldata f, uint256[] calldata v, bool[] calldata r, bytes[] calldata d) external {
        target = t; kinds = k; froms = f; values = v; rets = r; at = 0;
        delete datas;
        delete oks;
        for (uint256 i; i < d.length; i++) datas.push(d[i]);
        step();
        require(at == kinds.length, "director: the script is left over");
    }
    function step() internal {
        uint256 i = at++;
        require(kinds[i] == 0, "director: a return outside a call");
        oks.push(Agent(payable(froms[i])).act(target, values[i], datas[i]));
    }
    function onCall() external returns (bool) {
        while (at < kinds.length) {
            if (kinds[at] == 1) return rets[at++];
            step();
        }
        return true;
    }
    function count() external view returns (uint256) { return oks.length; }
}
