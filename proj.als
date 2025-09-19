sig Key {}

sig Val {}

sig Server {

nxt: lone Server,

store: Key-> lone Val

}

sig SActive, SInactive in Server {}

sig Client {

srvr: lone Server

}

sig CActive, CInactive in Client {}

fact{

CActive + CInactive = Client
SActive + SInactive = Server

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


run { #Server >= 4 &&  #Client >= 6 } for 7
