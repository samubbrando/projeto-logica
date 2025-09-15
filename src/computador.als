module Computador

abstract sig Computador{}

one sig Lenovo,Dell,Apple,Acer extends Computador{}

sig Rapido,Memoria,Compacto in Computador{}

pred isIdeal[c:Computador]{
	c in Rapido and c in Memoria and c in Compacto
}

fact {

	one c:Computador | isIdeal[c]
	(#Rapido = 3) and (#Memoria = 2) and (#Compacto=1)
	all c:Computador | (c in Rapido) or (c in Memoria) or (c in Compacto)
	(Lenovo in Memoria) iff (Dell in Memoria)
	(Apple in Rapido) iff (Dell in Rapido)
	!((Apple in Rapido) iff (Acer in Rapido))
		

}

run {
} 
