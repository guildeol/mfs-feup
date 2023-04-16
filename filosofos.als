// Modelo do jantar dos filósofos

// As "coisas" à volta da mesa
abstract sig Coisa {
	prox : one Coisa
}

sig Filosofo extends Coisa {
	// Garfos que cada filósofo tem na mão
	var garfos : set Garfo
}

sig Garfo extends Coisa {}

// Especifique a configuração da mesa
fact Mesa {
	// A mesa é redonda, ou seja, as coisas formam um anel
	always(Coisa in Coisa.^prox)

	// Os garfos e os filósofos estão intercalados
	always(all f:Filosofo | f.prox in Garfo)
	always(all g:Garfo| g.prox in Filosofo)

	// Todos os Filosofos e todos os Garfos estao na Mesa
	always(all f:Filosofo | (Filosofo - f) in f.^prox)
	always(all g:Garfo| (Garfo - g) in g.^prox)
	
	// Um filosofo tem no máximo dois garfos
	always(all f:Filosofo | #(f.garfos) <=2)

	// Os garfos que os filosofos pegam estao proximos a eles, ou nao existem
	always(all f:Filosofo, g:f.garfos | g in (f.prox + f.~prox) or no g)

	// Nenhum garfo esta com dois filosofos ao mesmo tempo
	always(all disj f1, f2:Filosofo | (f1.garfos & f2.garfos) = none)

	// Existe ao menos um garfo
	#(Garfo) > 1
}

// Especifique os seguintes eventos

// Um filosofo pode comer se já tiver os dois garfos junto a si
// e pousa os garfos depois
pred come [f : Filosofo] {
	//Guard
	#(f.garfos) = 2

	// Effect
	f.garfos' = none

	// Frame Conditions
	(Filosofo - f).garfos' = (Filosofo - f).garfos
}

pred NotWithMe[f:Filosofo, g:Garfo] {
	g not in f.garfos
}

pred NotWithOthers[f:Filosofo, g:Garfo] {
	g not in (Filosofo - f).garfos
}

pred WithMe[f:Filosofo, g:Garfo] {
	g in f.garfos
}

pred WithOthers[f:Filosofo, g:Garfo] {
	g in (Filosofo - f).garfos
}

// Um filósofo pode pegar num dos garfos que estejam
// pousados junto a si
pred pega [f : Filosofo] {
	{
		// Guard
		NotWithMe[f, f.prox] and NotWithOthers[f, f.prox]
		// Effect
		f.garfos' = f.garfos + f.prox
		// Frame Conditions
		(Filosofo - f).garfos' = (Filosofo - f).garfos
	} 
	or
	{
		// Guard
		NotWithMe[f, f.~prox] and NotWithOthers[f, f.~prox]
		// Effect
		f.garfos' = f.garfos + f.~prox
		// Frame Conditions
		(Filosofo - f).garfos' = (Filosofo - f).garfos
	}
}

// Para além de comer ou pegar em garfos os filósofos podem pensar
pred pensa [f : Filosofo] {
	garfos' = garfos
}

fact Comportamento {
	// No inicio os garfos estão todos pousados
	no garfos
	// Depois os filósfos só podem comer, pegar ou pensar
	always (some f : Filosofo | come[f] or pega[f] or pensa[f])
}

// Especifique as seguintes propriedades
pred fairness {
	all f:Filosofo | always eventually #(f.garfos) = 2 implies after come[f]
	all f:Filosofo | always eventually #(f.garfos) = 0 implies eventually pega[f]
}

assert GarfosNaMao {
	// O mesmo garfo nunca pode estar na mão de dois filósofos
	always(all g:Garfo | all disj f1, f2:Filosofo | g in f1.garfos implies g not in f2.garfos)
}
check GarfosNaMao for 6

assert SempreQuePegaCome {
	// Qualquer filósofo que pega num garfo vai conseguir comer
	fairness implies always (all f:Filosofo | #(f.garfos) = 1 implies eventually(come[f]))
}
check SempreQuePegaCome for 6

assert SemBloqueio {
	fairness implies eventually(all f:Filosofo | come[f] or pega[f])
}
check SemBloqueio for 6

// Especifique um cenário com 4 filósofos onde todos conseguem comer
run TodosComem {
	all f:Filosofo | eventually(come[f])
} for exactly 8 Coisa, 4 Filosofo, 20 steps

run AlguemPega{
	some f:Filosofo | eventually(pega[f])
} for exactly 4 Coisa, 2 Filosofo

run AlguemCome{
	some f:Filosofo | eventually(come[f])
} for 20 steps, exactly 4 Coisa, 2 Filosofo

run AlguemPegaDois{
	some f:Filosofo | eventually(#(f.garfos) = 2)
} for exactly 8 Coisa, 4 Filosofo
