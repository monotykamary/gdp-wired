import concurrent.futures, hashlib, pathlib, re, urllib.request
root=pathlib.Path('.')
files=['Consensus.tla','TCommit.tla','lockserver.tla','quorum_leader_election.tla','toy_consensus_forall.tla','Simple.tla','SimpleRegular.tla','lockserv_automaton.tla','sharded_kv.tla','sharded_kv_no_lost_keys.tla','lockserv.tla','TwoPhase.tla','simple_decentralized_lock.tla','two_phase_commit.tla','consensus_wo_decide.tla','consensus_forall.tla','naive_consensus.tla','client_server_ae.tla','client_server_db_ae.tla','simple_election.tla','toy_consensus_epr.tla','toy_consensus.tla','firewall.tla','majorityset_leader_election.tla','consensus_epr.tla','learning_switch.tla','learning_switch_i4.tla','MongoLoglessDynamicRaft.tla','paxos_epr.tla']
base='https://raw.githubusercontent.com/will62794/endive/8b6f2abd1988eeb308f965813635e9871f253e2d/benchmarks/'
urls=[(f,base+f) for f in files]+[('paxos_epr.pyv','https://raw.githubusercontent.com/wilcoxjay/mypyvy/12a8f5434a25587c56814d090b6ab7fa95851e71/examples/pd/paxos_epr.pyv')]
def fetch(pair):
 name,url=pair
 try:
  b=urllib.request.urlopen(url,timeout=30).read(); text=b.decode(); return name,url,hashlib.sha256(b).hexdigest(),text
 except Exception as e:return name,url,'FAILED',str(e)
for name,url,h,text in concurrent.futures.ThreadPoolExecutor(max_workers=6).map(fetch,urls):
 print('SOURCE',name,url,'SHA256',h)
 for i,line in enumerate(text.splitlines(),1):print(f'{name}:{i}: {line}')
for name in ['research/protocols/ic3syn/models.ts','research/protocols/ic3syn/common.ts','research/protocols/ic3syn/run.ts','research/protocols/models.ts']:
 b=(root/name).read_bytes(); print('LOCAL_SHA256',name,hashlib.sha256(b).hexdigest())
 for i,line in enumerate(b.decode().splitlines(),1):
  if re.search(r'\.(assume|facts|pre|prune|keep)\s*\(|\bkeep:|\blaws:|process\.env|readFile|seed',line): print('INVENTORY',name,i,line)
