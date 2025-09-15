open util/ordering[Estado] as est

-- Assinaturas básicas
abstract sig Cliente {
  idade: one Int
}

sig ClientePreferencial extends Cliente {} {
  idade >= 50
}

sig ClienteRegular extends Cliente {} {
  idade < 50
}

abstract sig Apartamento {
  moradores: set Cliente
}

sig Apartamento2Quartos extends Apartamento {} {
  #moradores <= 2
}

sig Apartamento3Quartos extends Apartamento {} {
  #moradores <= 3
}

sig Cobertura extends Apartamento {} {
  #moradores <= 2
  all m: moradores | m in ClientePreferencial
}

-- Estado do sistema
sig Estado {
  clientes: set Cliente,
  aptos2q: set Apartamento2Quartos,
  aptos3q: set Apartamento3Quartos,
  cobertura: lone Cobertura,
  listaEspera: set Cliente,
  alugueisAtivos: set Apartamento
}

-- Fatos do sistema
fact ConfiguracaoInicial {
  -- Quantidade fixa de apartamentos
  #Apartamento2Quartos = 3
  #Apartamento3Quartos = 2
  one Cobertura
  
  -- Estado inicial vazio
  first.clientes = none
  first.aptos2q = Apartamento2Quartos
  first.aptos3q = Apartamento3Quartos
  first.cobertura = Cobertura
  first.listaEspera = none
  first.alugueisAtivos = none
}

fact RegrasDeTransicao {
  all e: Estado - last | let e = e.next {
    -- Um cliente pode chegar
    (some novoCliente: Cliente - e.clientes | {
      e'.clientes = e.clientes + novoCliente
      e'.listaEspera = e.listaEspera
      e'.alugueisAtivos = e.alugueisAtivos
      e'.aptos2q = e.aptos2q
      e'.aptos3q = e.aptos3q
      e'.cobertura = e.cobertura
    })
    
    or
    
    -- Alugar apartamento de 2 quartos
    (some cliente: e.clientes - e.alugueisAtivos.moradores, apto: e.aptos2q | {
      e'.aptos2q = e.aptos2q - apto
      e'.alugueisAtivos = e.alugueisAtivos + apto
      apto.moradores = cliente
      e'.clientes = e.clientes
      e'.listaEspera = e.listaEspera
      e'.aptos3q = e.aptos3q
      e'.cobertura = e.cobertura
    })
    
    or
    
    -- Alugar apartamento de 3 quartos
    (some cliente: e.clientes - e.alugueisAtivos.moradores, apto: e.aptos3q | {
      e'.aptos3q = e.aptos3q - apto
      e'.alugueisAtivos = e.alugueisAtivos + apto
      apto.moradores = cliente
      e'.clientes = e.clientes
      e'.listaEspera = e.listaEspera
      e'.aptos2q = e.aptos2q
      e'.cobertura = e.cobertura
    })
    
    or
    
    -- Alugar cobertura (apenas clientes preferenciais)
    (some clientesPref: e.clientes & ClientePreferencial - e.alugueisAtivos.moradores, 
         cob: e.cobertura | #clientesPref <= 2 and {
      e'.cobertura = none
      e'.alugueisAtivos = e.alugueisAtivos + cob
      cob.moradores = clientesPref
      e'.clientes = e.clientes
      e'.listaEspera = e.listaEspera
      e'.aptos2q = e.aptos2q
      e'.aptos3q = e.aptos3q
    })
    
    or
    
    -- Entrar na lista de espera quando não há apartamentos
    (some cliente: e.clientes - e.alugueisAtivos.moradores - e.listaEspera | 
     e.aptos2q = none and e.aptos3q = none and e.cobertura = none and {
      e'.listaEspera = e.listaEspera + cliente
      e'.clientes = e.clientes
      e'.alugueisAtivos = e.alugueisAtivos
      e'.aptos2q = e.aptos2q
      e'.aptos3q = e.aptos3q
      e'.cobertura = e.cobertura
    })
    
    or
    
    -- Prioridade para clientes preferenciais na lista de espera
    (some clientePref: e.listaEspera & ClientePreferencial, 
         apto: Apartamento - e.alugueisAtivos | {
      e'.listaEspera = e.listaEspera - clientePref
      apto in Apartamento2Quartos implies e'.aptos2q = e.aptos2q - apto
      apto in Apartamento3Quartos implies e'.aptos3q = e.aptos3q - apto
      apto in Cobertura implies e'.cobertura = none
      e'.alugueisAtivos = e.alugueisAtivos + apto
      apto.moradores = clientePref
      e'.clientes = e.clientes
    })
  }
}

-- Predicados para testes
pred mostrarSistema {
  some Estado
  some Cliente
}

pred testarAluguelCobertura {
  some e: Estado | some e.cobertura.moradores
  some ClientePreferencial
}

pred testarListaEspera {
  some e: Estado | some e.listaEspera
}

pred testarPrioridadePreferenciais {
  some e: Estado | some e.listaEspera & ClientePreferencial
}

-- Executar
run mostrarSistema for 5 but 10 Estado
run testarAluguelCobertura for 5 but 10 Estado
run testarListaEspera for 5 but 10 Estado  
run testarPrioridadePreferenciais for 5 but 10 Estado

-- Asserções para verificar propriedades
assert CoberturaApenasPreferenciais {
  all e: Estado, c: e.alugueisAtivos & Cobertura |
    all m: c.moradores | m in ClientePreferencial
}

assert LimiteMoradores {
  all a: Apartamento |
    (a in Apartamento2Quartos implies #a.moradores <= 2) and
    (a in Apartamento3Quartos implies #a.moradores <= 3) and
    (a in Cobertura implies #a.moradores <= 2)
}

assert ClienteApenasUmApartamento {
  all e: Estado | all c: e.clientes |
    lone a: e.alugueisAtivos | c in a.moradores
}

-- Verificar asserções
check CoberturaApenasPreferenciais for 5
check LimiteMoradores for 5
check ClienteApenasUmApartamento for 5
