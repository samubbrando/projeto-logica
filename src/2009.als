module imobiliaria

open util/integer

// Imobiliária
one sig Imobiliaria {
    	apartamentos: set Apartamento,
    	clientes: set Cliente,
    	listaDeEspera: set Cliente
}

// Cliente
abstract sig Nome {}

abstract sig Cliente {
    	nome: one Nome
}

sig ClienteRegular extends Cliente {}
sig ClientePreferencial extends Cliente {}

fact nomesUnicos {
    all n: Nome | one c: Cliente | c.nome = n
}

// Apartamento

sig Quarto {}
sig Suite extends Quarto {}

abstract sig Apartamento {
	quartos: set Quarto,
    	moradores: set Cliente
}

sig Apt2Quartos extends Apartamento {}
sig Apt3Quartos extends Apartamento {}
one sig Cobertura extends Apartamento {}

fact numeroDeImoveis {
	(#Apt2Quartos = 3) and (#Apt3Quartos = 2)
}

fact quartosPorApt {
	all q: Quarto | one a: Apartamento | q in a.quartos
}

fact configuracaoDeQuartos {
    all a: Apt2Quartos | 
        # (a.quartos & Suite) = 1 and    // 1 suíte
        # (a.quartos - Suite) = 1        // 1 quarto normal
    all a: Apt3Quartos | 
        # (a.quartos & Suite) = 2 and    // 2 suíte
        # (a.quartos - Suite) = 1        // 1 quarto normal
}


// ===== FATOS =====

fact prioridadeAluguel {
    not (
        (some cr: ClienteRegular | some cr.~moradores) and
        (some cp: ClientePreferencial | no cp.~moradores)
    )
}

fact restricaoDeAluguel {
	all c: Cliente | one a: Apartamento | c in a.moradores
}

fact contidosNaImobiliaria {
    Cliente in Imobiliaria.clientes
    Apartamento in Imobiliaria.apartamentos
}

run {} for 12 but 13 Int
