sig Workstation {
	workers : set Worker,
	succ : set Workstation
}
one sig begin, end in Workstation {}

sig Worker {}
sig Human, Robot extends Worker {}

abstract sig Product {
	parts : set Product	
}

sig Material extends Product {}

sig Component extends Product {
	workstation : set Workstation
}

sig Dangerous in Product {}

// Specify the following properties
// You can check their correctness with the different commands and
// when specifying each property you can assume all the previous ones to be true

pred inv1 {
  // Workers are either human or robots
  
  // all w:Worker | w in (Human + Robot)
  Worker = Human + Robot
  // Worker in Human + Robot
  // all w:Worker | w in Human and w in Robot
  // no (Worker - Human - Robot)
}


pred inv2 { 
  // Every workstation has workers and every worker works in one workstation
  // workers in Workstation one -> some Worker
  all w:Worker | one workers.w
  // all w:Worker | one w.~workers  
  // all w:Workstation | some w.workers 
  Workstation = workers.Worker // The set of workstations is equal to the set with workstation with workers assigned to them.
}


pred inv3 {
  // Every component is assembled in one workstation
  // workstation in Component -> one Workstation
  all c:Component | one c.workstation
}


pred inv4 {
  // Components must have parts and materials have no parts
  all c:Component | some c.parts
  all m:Material | no m.parts
  
  // parts in Component -> some Product
  
  // Component = parts.Product
}


pred inv5 {
  // Humans and robots cannot work together
  // all s:Workstation, h:Human, r:Robot |h not in s.workers or r not in s.workers
  // all s:Workstation | s.workers in Human or s.workers in Robot
  no (workers.Human & workers.Robot)
}


pred inv6 {
  // Components cannot be their own parts
  all c:Component | c not in c.^parts
  
  // no iden & ^parts
}


pred inv7 {
  // Components built of dangerous parts are also dangerous
  
  // parts.Dangerous in Dangerous
  all c:Component | some (c.parts & Dangerous) implies c in Dangerous
}


pred inv8 {
  // Dangerous components cannot be assembled by humans
  // all c:Dangerous, ws:c.workstation | no ws.workers & Human
  // all c:Dangerous | no c.workstation.workers & Human
  no Dangerous.workstation.workers & Human
}


pred inv9 {
  // The workstations form a single line between begin and end
  all w:Workstation - end | one w.succ // All workstations except end have a succ
  no end.succ
  Workstation in begin.*succ
}


pred inv10 {
	// The parts of a component must be assembled before it in the production line
}
