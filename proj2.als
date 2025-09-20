sig Key {}

sig Val {}

sig Server {

	var nxt: lone Server,
	var store: Key-> lone Val,
	var sInbox: set Request
}

var sig SActive, SInactive in Server {}

sig Client {

	var srvr: lone Server,
	//var cInbox: set Response,
	var cOutbox: set Request
}

var sig CActive, CInactive in Client {}

abstract sig Request{

	key: Key,
	val: lone Val,
	var client: lone Client,
	reqSrvr: lone Server
}

sig ReqFind, ReqStore, OpFind, OpStore extends Request{}

sig Response{

	key: Key,
	val: lone Val
}

sig StoreSuc, StoreFail, FindSuc, FindFail extends Response{}


pred init{

	one SActive
	nxt = SActive -> SActive
	
	no sInbox
	//no cInbox
	some cOutbox
	//no store
	all r: Request | one c: Client | r in c.cOutbox and (r in ReqFind or r in ReqStore) and no r.client and no r.reqSrvr

}

pred stutter[]{
	nxt' = nxt
	store' = store
	sInbox' = sInbox
	//cInbox' = cInbox
	cOutbox' = cOutbox
	client' = client
	srvr' = srvr
	SActive' = SActive
	SInactive' = SInactive
	CActive' = CActive
	CInactive' = CInactive
}

pred trans[]{
	stutter[]
	||
	some s1,s2 : Server | connect_server[s1,s2]
	||
	some c : Client , s : Server | connect_client[c,s]
	||
	some  c : Client , r : Request | send_request[c,r]
	||
	some s : Server, r : Request | process[s,r]
}

pred valid[] {
	Server = SActive + SInactive
	no SActive & SInactive
	Client =  CActive + CInactive
	no CActive & CInactive

	//nenhum server inactive pode ter um next
	no SInactive.nxt

	//nenhum server inactive pode ter algum client a apontar para ele
	no SInactive.~nxt
	
	//nenhum cliente inactive pode ter um server associado
	no CInactive.srvr

	//pnenhum cliente inactive pode estar ligado a um server inactive
	no SInactive.~srvr

	//serveres inativos nao podem ter entradas
	no SInactive.store

	all c : CActive | one c.srvr

	//serve para criar a conexao em ciclo
	all s : SActive  | s.^nxt = SActive

	//lone or one 
	all k : Key |  lone s : Server |  some k.(s.store)
}

pred system[]{
	init[]
	&&
	always trans[]
	&&
	always valid[]
}

pred connect_server[s1 : Server, s2 : Server]{
	//pre conditions
	s1 in SActive
	s2 in SInactive
	
	//post conditions
	SActive' = SActive + s2
	SInactive' = SInactive - s2
	nxt' = nxt + (s2 -> s1.nxt) - (s1 -> s1.nxt) + (s1 -> s2)
	
	//frame 
	store' = store
	sInbox' = sInbox
	//cInbox' = cInbox
	cOutbox' = cOutbox
	client' = client
	srvr' = srvr
	CActive' = CActive
	CInactive' = CInactive
}

pred connect_client[c : Client, s : Server]{
	//pre conditions
	c in CInactive
	s in SActive
	
	//post conditions
	CActive' = CActive + c
	CInactive' = CInactive - c
	srvr' = srvr + (c -> s)
	
	//frame 
	store' = store
	sInbox' = sInbox
	//cInbox' = cInbox
	cOutbox' = cOutbox
	client' = client
	SActive' = SActive
	SInactive' = SInactive
	nxt' = nxt
}

pred send_request[c:Client, r: Request]{
	send_store_request[c,r]
	||
	send_find_request[c,r]
}

pred send_store_request[c: Client, r: Request]{
	//pre conditions
	c in CActive
	r in c.cOutbox
	r in ReqStore
	one r.val
	no r.reqSrvr
	no r.client

	//post conditions
	client' = client + (r -> c)
	cOutbox' = cOutbox - (c->r)
	sInbox' = sInbox + (c.srvr->r)
	
	//frame 
	store' = store
	//cInbox' = cInbox
	SActive' = SActive
	SInactive' = SInactive
	CActive' = CActive
	CInactive' = CInactive
	nxt' = nxt
	srvr' = srvr
	
}

pred send_find_request[c: Client, r: Request]{
	//pre conditions
	c in CActive
	r in c.cOutbox
	r in ReqFind
	no r.val
	no r.reqSrvr
	no r.client

	//post conditions
	client' = client + (r -> c)
	cOutbox' = cOutbox - (c->r)
	sInbox' = sInbox + (c.srvr->r)
	
	//frame 
	store' = store
	//cInbox' = cInbox
	SActive' = SActive
	SInactive' = SInactive
	CActive' = CActive
	CInactive' = CInactive
	nxt' = nxt
	srvr' = srvr
	
}

pred process[s: Server, r: Request]{
	
	process_store_req[s,r]
	//||
	//process_store_op[s]
	||
	process_find_req[s,r]
	//||
	//process_store_req[s]
	
}

pred process_store_req[s: Server, r: Request]{

	process_store_req_has_key[s,r]
}

pred process_store_req_has_key[s: Server, r: Request]{
	//pre conditions
	s in SActive
	r in s.sInbox
	r in ReqStore
	some v: Val | r.key->v in s.store

	//acho q n é preciso verificar que nao tem server e tem cliente e val porque é verificado no envio do cliente e o req só pode vir a partir desse envio

	//post conditions
	store' = store - (s -> r.key -> Val) + (s -> r.key -> r.val)
	sInbox' = sInbox - (s->r)
	//enviar para o client
	
	//frame
	nxt' = nxt
	//cInbox' = cInbox
	cOutbox' = cOutbox
	client' = client
	srvr' = srvr
	SActive' = SActive
	SInactive' = SInactive
	CActive' = CActive
	CInactive' = CInactive
	
}

pred process_find_req[s: Server, r: Request]{

	process_find_req_has_key[s,r]
	//||
	//process_find_req_no_key[s,r]
}

pred process_find_req_has_key[s: Server, r: Request]{
	//pre conditions
	s in SActive
	r in s.sInbox
	r in ReqFind
	some v: Val | r.key->v in s.store
	
	//post conditions
	sInbox' = sInbox - (s->r)
	//enviar para o client

	//frame
	nxt' = nxt
	//cInbox' = cInbox
	cOutbox' = cOutbox
	client' = client
	srvr' = srvr
	store' = store
	SActive' = SActive
	SInactive' = SInactive
	CActive' = CActive
	CInactive' = CInactive
	
}

fact {
	system[]
}

run { #Response = 0 and #Key = 2 and #Val = 3 and #Server = 1 and #Client = 4 and #SInactive = 0 and #CInactive = 0 and eventually (some s : Server, r : Request | process_find_req_has_key[s,r]) } for 6

//pending store keys for each server
//if receives storeOp for k1 and has k1 on pending, sends store fail to client and server that started (he removes its pending)
