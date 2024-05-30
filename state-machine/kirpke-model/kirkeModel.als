module KirkeModel

sig Prop {}

sig State {
    labels : set Prop -- those propositions that are true at this state
}

sig StateMachine {
    states : set State,
    init, final : set states,
    next : states -> states
} {
    some init
}

// s = m.init.^(m.next) -- All states reachable from init by one or more steps
pred Reaches[m : StateMachine, s : set State] {
    s = m.init.*(m.next) -- All states reachable from init by zero or more steps (includes init)
} run Reaches for 3 but 1 StateMachine

pred DeadlockFree[m : StateMachine] {
    // All states reachable from the initial state
    // let reachable = m.init.*(m.next) |
        // Among those reachable states, there is no state from which no further transition is possible
        no s : State - m.init |
            no s.(m.next)
} run DeadlockFree for 3 State, 1 StateMachine

pred Deterministic[m : StateMachine] {
    all x : m.init.*(m.next) | lone x.(m.next)
} run Deterministic for 3 but 1 StateMachine

pred Reachability[m: StateMachine, p: Prop] {
    some s : m.init.*(m.next) |
        p in s.labels
} run Reachability for 3 but 1 StateMachine

pred Liveness[m: StateMachine, p: Prop] {
    all x : m.init.*(m.next) | 
        some y : x.*(m.next) | 
            p in y.labels
} run Liveness for 3 but 1 StateMachine

assert Implies {
    all m : StateMachine, p : Prop | Liveness[m, p] => Reachability[m ,p]
} check Implies for 3 but 1 StateMachine


assert Converse {
    all m : StateMachine, p : Prop | Reachability[m, p] => Liveness[m ,p]
} check Converse for 3 but 1 StateMachine


// pred SimulationForFiveDf[m : StateMachine] {
//     # states = 3
//     some x : m.states | not lone x.(m.next)
//     all x : m.states | no x.(x.next) => x in final
//     all x, y : m.states | 
//     { p : Prop | p in x.labels } = { p : Prop | p in y.labels } => x = y
// } run SimulationForFiveDf for 3 but 1 StateMachine

pred SimulationForDeadlockFree[m: StateMachine] {
    #states = 3 // Change this number as needed
    some x: m.states | not lone x.(m.next)
    all x: m.states | no x.(m.next) => x in m.final
    all x, y: m.states | { p: Prop | p in x.labels } = { p: Prop | p in y.labels } => x = y
} run SimulationForDeadlockFree for 3 but 1 StateMachine

// Predicate: Check if the state machine satisfies simulation for determinism
pred SimulationForDeterministic[m: StateMachine] {
    #states = 3 // Change this number as needed
    all x: m.states | lone x.(m.next)
} run SimulationForDeterministic for 3 but 1 StateMachine

// Predicate: Check if the state machine satisfies simulation for liveness
pred SimulationForLiveness[m: StateMachine, p: Prop] {
    #states = 3 // Change this number as needed
    all x: m.init.*(m.next) | some y: x.*(m.next) | p in y.labels
} run SimulationForLiveness for 3 but 1 StateMachine
