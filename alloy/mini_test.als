abstract sig Action {
	requires : set Action
}

sig Activate, Move, Rotate extends Action {}

sig Mission {
	actions : set Action,
	var executing : one Action,
	var actionLog : set Action,
}

fact NoLooseSigs
{
	all a:Action | a in Mission.actions or no a
}

pred endpoints[m:Mission] {
	some disj a1, a2:m.actions | (no a1.requires) and (no a2.~requires)
}

pred integrity[m:Mission] {
	all a:m.actions | a.^requires in m.actions
}

pred acyclic[m:Mission] {
	all a:m.actions | a not in a.requires and a not in a.^requires
}


fact Conditions
{
	always (all m:Mission | endpoints[m] and integrity[m] and acyclic[m])
}

// Events
pred init[m:Mission] {
	some m.executing and no m.executing.requires
  	no m.actionLog
}

pred next[m:Mission]
{
	some m.executing

	m.actionLog' = m.actionLog + m.executing and
	m.executing' = one (a:(m.actions - m.executing) | a.requires in m.actionLog)
}

fact Traces
{
	all m:Mission | init[m]
	always(some m:Mission | next[m])
}

// Runs and checks
run Test {
	all m:Mission | endpoints[m] and acyclic[m] and integrity[m]
} for exactly 1 Mission, exactly 5 Action

pred DAG[m:Mission] {
	all a:m.actions | a in m.actions.^requires
}

run SharedAction {
	some a:Action, m1, m2:Mission | a in m1.actions and a in m2.actions
}

run EventuallyMeetsRequirements {
	some m:Mission, a:m.actions | a.requires != none and eventually (a.requires in m.actionLog)
} for exactly 1 Mission, exactly 5 Action

assert AllExecutedBeenInExecuting {
	always (all m:Mission, a:Action | a in m.actionLog iff historically(a in m.executing))
}
check AllExecutedBeenInExecuting for exactly 1 Mission, exactly 5 Action
