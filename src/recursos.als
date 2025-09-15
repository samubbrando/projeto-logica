module blocoCP

sig Recurso{
	recursoSuperior: lone Recurso
}

sig Usuario{
	temAcesso: set Recurso
	
}

sig Local{
	recursos: set Recurso,
	usuarios: set Usuario

}

fact Restricoes {

	all l1,l2: Local | !(l1 = l2) implies no (l1.recursos & l2.recursos)
	all r: Recurso | some recursos.r

	-- por que nao funcionou?	
	all r:Recurso | !(r in r.(^recursoSuperior))

	
}

assert SemRecursoOrfao {
	no r: Recurso | no recursos.r
--	all r: Recurso | some recursos.r
}

assert semCiclo{
	no r: Recurso | r in r.recursoSuperior or r in r.recursoSuperior.recursoSuperior
}




check SemRecursoOrfao for 10

check semCiclo for 5


run {
	#Recurso = 3
--	all r:Recurso | some r.recursoSuperior
}
