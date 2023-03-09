// Modelo abstracto de um sistema de emissão de cartões bancários

abstract sig Status {}
one sig Unissued, Issued, Cancelled extends Status {}

sig Card {
	var status : one Status
}

sig Client {
	var cards : set Card
}

// Algumas das propriedades desejadas para o sistema

assert NoUnissuedCards {
	// Os clientes nunca podem deter cartões unissued
  always (Unissued not in Client.cards.status)
  //always all c:Client, r:c.cards | r.status != Unissued
}

assert NoSharedCards {
	// Ao longo da sua existência um cartão nunca pode pertencer a mais do que um cliente
  always (all c:Client, r:Card | r in c.cards
  implies 
  always r not in (Client - c).cards)
}

// Especifique as condições iniciais do sistema

fact Init {
  no cards // Initially, no card have been assinged to a client
  all c:Card | c.status = Unissued // All cards are currently unissued
}

// Especifique as operações do sistema por forma a garantir as propriedades
// de segurança

check NoUnissuedCards
check NoSharedCards

// Operação de emitir um cartão para um cliente
pred emit [c : Card, a : Client] {
  // Guards
  historically c.status = Unissued

  // effect
  cards' = cards + a -> c
  status' = status - c -> Unissued + c -> Issued
  // c.status' = Issued
  // a.cards' = a.cards + c

  // frame condition
  // all c2:Card - c | c.status' = c.status
  // all a2:Client -a >  a.cards' = a.cards
}

// Operação de cancelar um cartão
pred cancel [c : Card] {
  // guard
  c.status = Issued

  // effect
  status' = status - c -> Issued + c -> Cancelled

  // frame condition
  cards' = cards
}

pred nop {
	status' = status
	cards' = cards
}

fact Traces {
	always (nop or some c : Card | cancel[c] or some a : Client | emit[c,a])
}

// Especifique um cenário onde 3 cartões são emitidos a pelo menos 2
// clientes e são todos inevitavelmente cancelados, usando os scopes
// para controlar a cardinalidade das assinaturas
// Tente também definir um theme onde os cartões emitidos são verdes
// e os cancelados são vermelhos, ocultando depois toda a informação que
// seja redundante 
// Pode introduzir definições auxiliares no modelo se necessário

run Exemplo {
  all c:Card | eventually cancel[c]
} for exactly 3 Card, exactly 2 Client

