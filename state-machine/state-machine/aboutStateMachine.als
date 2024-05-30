module AboutStateMachine

sig State {}        -- simple states

sig StateMachine {  -- composite state machines
    A : set State,   -- set of states of a state machine
    i : A,           -- initial state of a state machine
    F : set A,       -- set of final states of a state machine
    R : A -> A       -- transition relation of a state machine
}

-- Claim that final states are never initial: False
assert FinalNotInitial {
    all M : StateMachine | no M.i & M.F
} check FinalNotInitial for 3 but 1 StateMachine

-- Is there a three-state machine with a non-final deadlock?: True
-- Consistency Check named "AGuidedSimulation"
pred AGuidedSimulation[M : StateMachine, s: M.A] {  -- "M" is of type StateMachine, "s" is a state of "M"
    no s.(M.R)      -- no transition out of state "s" or there is no M.R-transition from "s" to "s"
    not s in M.F    -- "s" is a non-final state of "M"
    # M.A = 3       -- consistency check with a finite list of constraints (3)
} run AGuidedSimulation for 3 but 1 StateMachine
