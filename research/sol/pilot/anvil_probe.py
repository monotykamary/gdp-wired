import sys, json, time
sys.path.insert(0, 'core/sol')
import harness as h
h.S['addrBits'] = 26
h.start_anvil()
frm = h.addr_hex(5)
h.fund(frm, 0)
print('bal', h.rpc('eth_getBalance', [frm, 'latest']))
print('gasPrice', h.rpc('eth_gasPrice', []))
blk = h.rpc('eth_getBlockByNumber', ['latest', False]); print('basefee', blk.get('baseFeePerGas'))
tx = {'from': frm, 'data': '0x6080604052348015600e575f5ffd5b50603e80601a5f395ff3fe60806040525f5ffdfea2646970667358221220', 'value': '0x0', 'gas': hex(3_000_000), 'gasPrice': '0x0'}
try:
  hh = h.rpc('eth_sendTransaction', [tx]); print('hash', hh)
  print('receipt', h.rpc('eth_getTransactionReceipt', [hh]))
  print('tx', h.rpc('eth_getTransactionByHash', [hh]))
except Exception as e: print('err', e)
h.S['anvil'].kill()
