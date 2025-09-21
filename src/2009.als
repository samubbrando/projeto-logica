module imobiliaria

open util/integer

// ===== IDENTIDADES =====
sig Nome {}

abstract sig Categoria {}
one sig Ateh50, Entre50e60, Mais60 extends Categoria {}

sig Cliente {
    nome: one Nome,
    categoria: one Categoria
}

// ===== IMOBILIÁRIA =====
one sig Imobiliaria {
    apartamentos: set Apartamento,
    clientes: set Cliente,
    listaDeEspera: set Cliente
}

// ===== QUARTOS / APTOS =====
sig Quarto {
    ocupante: lone Cliente   // cada quarto tem no máximo 1 ocupante
}
sig Suite extends Quarto {}

abstract sig Apartamento {
    quartos: set Quarto,
    moradores: set Cliente,       // clientes efetivamente alocados (residentes)
    interessados: set Cliente    // clientes que têm interesse neste apto
}

sig Apt2Quartos extends Apartamento {}
sig Apt3Quartos extends Apartamento {}
one sig Cobertura extends Apartamento {}

// ===== ESPECIFICAÇOES DOS IMOVEIS =====
fact numeroDeImoveis {
    #Apt2Quartos = 3
    #Apt3Quartos = 2
}

fact configuracaoDeQuartos {
    // configuração das suítes / quartos por tipo de apto
    all a: Apt2Quartos |
        # (a.quartos & Suite) = 1 and
        # (a.quartos - Suite) = 1

    all a: Apt3Quartos |
        # (a.quartos & Suite) = 2 and
        # (a.quartos - Suite) = 1

    // cobertura: 4 quartos, sendo 3 suítes
    #Cobertura.quartos = 4
    # (Cobertura.quartos & Suite) = 3
    # (Cobertura.quartos - Suite) = 1
}

fact quartosCobremApartamentos {
    // cada quarto pertence exatamente a um apartamento
    all q: Quarto | one a: Apartamento | q in a.quartos
}

fact moradoresPorQuarto {
    // ligação entre quartos e moradores: moradores de um apto
    // são exatamente os ocupantes dos quartos desse apto
    all a: Apartamento |
        a.moradores = a.quartos.ocupante
}

fact contidosNaImobiliaria {
    Cliente in Imobiliaria.clientes
    Apartamento in Imobiliaria.apartamentos
    all a: Apartamento | a.moradores in Imobiliaria.clientes
}

// ===== REGRAS DE NEGÓCIO =====

// 1) Não alocar mais moradores do que quartos (garantido por moradoresPorQuarto)
// 2) moradores devem ser subset de interessados (aluguel só ocorre entre interessados)
fact moradoresSaoInteressados {
    all a: Apartamento | a.moradores in a.interessados
}

// 3) Preferência por idade:
//    - se houver interessado com >60 (Mais60) para um apto, então somente clientes Mais60 podem ser alocados naquele apto
//    - senão, se houver interessado na faixa 50-60, então não alocar clientes <50 quando houver candidatos 50-60
fact preferenciaIdade {
    all a: Apartamento |
        let m60 = a.interessados & { c: Cliente | c.categoria = Mais60 },
            m50 = a.interessados & { c: Cliente | c.categoria = Entre50e60 } |
        // se existe interessado >60, moradores devem vir apenas desse grupo
        (some m60) => (a.moradores in m60)
        &&
        // se não há >60, mas há 50-60, então moradores não podem ser da faixa Ateh50
        ((not (some m60) and some m50) => (all m: a.moradores | m.categoria != Ateh50))
}

// 4) Cobertura só pode ser alugada para clientes de prioridade
fact cobertura50eMais60 {
    (some Cobertura.moradores) => (all m: Cobertura.moradores | m.categoria in (Entre50e60 + Mais60))
}

// 5) Lista de espera: se todos os apartamentos estiverem lotados (todos os quartos ocupados),
fact listaDeEsperaQuandoLotado {
    (all a: Apartamento | all q: a.quartos | some q.ocupante) =>
        Imobiliaria.listaDeEspera = (Imobiliaria.apartamentos.interessados) - (Imobiliaria.apartamentos.quartos.ocupante)
}

run {} for 20
