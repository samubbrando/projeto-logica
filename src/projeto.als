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

sig ClienteRegular extends Cliente {} // < 50 anos
sig ClientePreferencial extends Cliente {} // >= 50 anos 

fact nomesUnicos {
    all n: Nome | one c: Cliente | c.nome = n
}

// Apartamento

sig Quarto {
    morador: lone Cliente
}
sig Suite extends Quarto {}

//Um cliente não pode morar em mais de um apartamento
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

// Os quartos devem ser ligados a um apartamento
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

// Apartamentos não alugados (ninguém está morando nele)
fact definirApartamentosLivres {
    Imobiliaria.apartamentosLivres = { a: Apartamento |
        all q: a.quartos | no q.morador
    }
}

// Lista de espera é formada por todo cliente que não está morando em um apartamento
fact definirListaDeEspera {
    Imobiliaria.listaDeEspera = { c: Cliente |
        no q: Quarto | q.morador = c
    }
}

// Só deve ter cliente na lista de espera quando todos os apartamentos estão alugados
fact semEsperaComApartamentoLivre {
    no Imobiliaria.apartamentosLivres or no Imobiliaria.listaDeEspera
}

// A corbetura só pode ter clientes preferenciais
fact restricaoCobertura {
    all q: Cobertura.quartos | 
        some q.morador implies q.morador in ClientePreferencial
}

// Os clientes e apartamento estão na imobiliária
fact contidosNaImobiliaria {
    Cliente in Imobiliaria.clientes
    Apartamento in Imobiliaria.apartamentos
}

//  Asserts

// O apartamento não pode ter mais moradores do que quartos
assert capacidadeRespeitada {
    all a: Apartamento |
        #a.quartos >= #(a.quartos.morador)
}

// Prioridade para o cliente preferencial (mais de 50 anos)
assert prioridadeRespeitada {
    (some cp: ClientePreferencial | no cp.~morador)
    implies (no cr: ClienteRegular | some cr.~morador)
}

// Clientes sem apartamento devem ficar na lista de espera
assert clientesNaListaDeEspera {
    all c: Cliente |
        (no q: Quarto | q.morador = c) implies c in Imobiliaria.listaDeEspera
}

check clientesNaListaDeEspera for 24
check capacidadeRespeitada for 24
check prioridadeRespeitada for 24

// Cenário exemplo

pred exemplo {
    some ClienteRegular
    and some ClientePreferencial

    and some a: Apt2Quartos |
        one q: a.quartos | q.morador in ClienteRegular

    and some b: Apt3Quartos |
        one s: b.quartos & Suite | s.morador in ClientePreferencial

    and some c: Cliente | no q: Quarto | q.morador = c
}

run exemplo for 24
