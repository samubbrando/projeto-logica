module fazendeiros

abstract sig Fazendeiro{}

one sig A,B,C extends Fazendeiro{}

one sig Dono in Fazendeiro{}

pred A1{C in Dono}
pred A2 {A !in Dono}
pred B1 {C !in Dono}
pred B2 { A in Dono}
pred C1 {C in Dono}
pred C2 { !B2 }

fact {
--	!( A1 iff A2) 
	
--	!( B1 iff B2)
--	!(C1 iff C2)

}

run{

--(!( A1 iff A2)) iff (A1 iff !A2)

}

assert Test{
	(!( A1 iff A2)) iff (A1 iff !A2)	
}

check Test for 3

