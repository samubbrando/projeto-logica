module imobiliaria

open util/integer

// Imobiliária
one sig Imobiliaria {
    	apartamentos: set Apartamento,
	apartamentosLivres: set Apartamento,
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

sig Quarto {
    morador: lone Cliente
}
sig Suite extends Quarto {}

fact restricaoDeAluguel {
	all c: Cliente | lone q: Quarto | q.morador = c
}

abstract sig Apartamento {
	quartos: set Quarto
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
    all c: Cobertura | 
        # (c.quartos & Suite) = 4 and    // 3 suíte
        # (c.quartos - Suite) = 1        // 1 quarto normal

}

// Fatos

fact prioridadeAluguel {
    not (
        (some cr: ClienteRegular | some cr.~morador) and
        (some cp: ClientePreferencial | no cp.~morador)
    )
}

fact definirApartamentosLivres {
    Imobiliaria.apartamentosLivres = { a: Apartamento |
        all q: a.quartos | no q.morador
    }
}

fact definirListaDeEspera {
    Imobiliaria.listaDeEspera = { c: Cliente |
        no q: Quarto | q.morador = c
    }
}

fact semEsperaComApartamentoLivre {
    no Imobiliaria.apartamentosLivres or no Imobiliaria.listaDeEspera
}

fact restricaoCobertura {
    all q: Cobertura.quartos | 
        some q.morador implies q.morador in ClientePreferencial
}

fact contidosNaImobiliaria {
    Cliente in Imobiliaria.clientes
    Apartamento in Imobiliaria.apartamentos
}

fact aa {
	all q: Cobertura.quartos | 
        some q.morador
}	

run {} for 24
