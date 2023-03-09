/* 
Complete o seguinte modelo de uma colónia de camaleões onde o número de 
camaleões é fixo mas onde a cor de cada camaleão pode mudar de acordo com
as seguintes regras: 
- As cores possíveis são Verde, Azul e Amarelo
- Se 2 camaleões de cores diferentes se encontram mudam ambos para a terceira cor
- As cores só se alteram na situação acima 
*/

abstract sig Cor {}
one sig Verde, Azul, Amarelo extends Cor {}

sig Camaleao {
  var cor : one Cor
}

pred nop {
	cor' = cor
}

pred encontro[x,y : Camaleao] {
	// Guard
	x.cor != y.cor

	// Effect
	x.cor' = Cor - (x + y).cor
	y.cor' = Cor - (x + y).cor

--	(x * y).cor' = Cor - (x + t).cor

	// Frame conditions
	-- cor' - (x + y) -> Cor = cor - (x + y) -> Cor
	all c:Camaleao - (x + y) | c.cor' = c.cor 
}

-- run { some x, y:Camaleao | eventually encontro[x, y]} for 5 but 20 steps

fact Comportamento {
	always
  (
    nop or
    some x,y : Camaleao | encontro[x, y]
  )
}

// Especifique as seguintes propriedades desta colónia

assert Estabilidade {
	// Se os camaleoes ficarem todos da mesma cor, as cores nunca mais mudam
	always (one Camaleao.cor implies always cor = cor')
}

check Estabilidade for 5

assert NaoConvergencia {
	// Se inicialmente há um camaleao verde e nenhum azul então não é possível
	// que a colónia fique toda amarela
--	(one cor.Verde and no cor.Azul) implies not eventually (Camaleao.cor = Amarelo)
	(one cor.Verde and no cor.Azul) implies always (Camaleao.cor != Amarelo)
}

check NaoConvergencia for 5

// Especifique um cenário onde existe um camaleao que não para de mudar de cor
// tomando: recorrentemente todas as cores possíveis

run Exemplo {
	some c:Camaleao | always (c.cor != c.cor' and c.cor' != c.cor'' and c.cor != c.cor'') // Changes on every state
}

