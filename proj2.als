sig Key {}

sig Val {}

sig Server {

	var nxt: lone Server,
	var store: Key-> lone Val,
	var sInbox: set Request
}

sig SActive, SInactive in Server {}

sig Client {

	var srvr: lone Server,
	var cInbox: set Response,
	var cOutbox: set Request
}

sig Request{

	key: Key,
	val: lone Val,
	client: Client
}

sig ReqFind, ReqStore in Request{}

sig OpFind in Request{

	findSrvr: Server //server que fez o find request
}

sig OpStore in Request{

	storeSrvr: Server //server que fez o store request
}

sig Response{

	key: Key,
	val: lone Val
}

sig StoreSuc, StoreFail, FindSuc, FindFail in Response{}

sig CActive, CInactive in Client {}

pred init{
	
	one SActive
	nxt = SActive -> SActive
	
	no sInbox
	no cInbox
	some cOutbox
}

pred trans[]{
	stutter[]
	||
	some s1,s2 : Server | connect_server[s1,s2]
	||
	some c : Client ,s : Server | connect_client[c,s]
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
	//sInbox' = sInbox
	//sInbox' = sInbox
	//cOutbox' = cOutbox
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
	//sInbox' = sInbox
	//sInbox' = sInbox
	//cOutbox' = cOutbox
	SActive' = SActive
	SInactive' = SInactive
	nxt' = nxt
}



fact {
	system[]
}

run {#Server = 4 and #Client = 4 and  eventually (SInactive = none and CInactive = none) } for 6

//pending store keys for each server
//if receives storeOp for k1 and has k1 on pending, sends store fail to client and server that started (he removes its pending)
