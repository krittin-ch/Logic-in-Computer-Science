module PDS

open util/ordering[Number] -- open specification template for linear order

sig Name, Service, Number {}

// "i: set S" means that "i" is a subset of set "S"
// "i: lone S" means that "i" is a subset of set "S" with at most one element (non-empty, singleton set)
// "i: S" means that "i" is a subset of "S" containing exactly one element; this really specifies a scalar/element of type "S" since Alloy identifies elements "a" with sets {"a"}

// "Component" offers services to other components
sig Component {
    name : Name,             -- name of the component
    main : lone Service,     -- component may have a "main" service
    export : set Service,    -- services the component exports
    import : set Service,    -- services the component imports
    version : Number         -- version number of the component
} { no import & export }

// Package Dependency System (PDS)
// The primary concern in a PDS is its set of components is coherent: at all times, all imports of all of its components can be serviced within that PDS
// "Integrity Constraint": for all component (c) in components, all c's needed services can be provided by some component in components as well

/*
    Given this integrity constraint we can already model the installation (adding) or removal of a component in a PDS, 
    without having specified the remaining structure of a PDS. 
    This is possible since, in the context of these operations, we may abstract a PDS into its set of components

*/ 

sig PDS {
    components : set Component,
    schedule : components -> Service -> lone components, -- "lone" indicates the multiplicity constraint, saying that each component of the PDS and each service get related to at most one component
    requires : components -> components
} {
    // components.import is the union of all sets component.import, as so components.export
    // Observe that this requirement does not specify which component provides which service, which would be an unacceptable imposition on implementation freedom

    /*
        for every component in the system,
        the services it imports are supplied (exported)
        by some (other) component in the system
    */
    components.import in components.export
}

// The Addition of a component to a PDS
// P is the PDS prior to the execution of that operation
// Px is the PDS after that execution
// c models the component that is to be added
/*
    P.schedule[c, s], P.schedule[c][s], and c.(P.schedule)[s] have the same meaning
    Also, c.(P.requires) have the same meaning as P.requires[c]
*/
pred AddComponent[P, Px : PDS, c : Component] {   -- The intents (variables) interprets the parametric constraint AddComponent as an operation leading from one "state" to another
    not c in P.components
    Px.components = P.components + c
} run AddComponent for 3

pred RemoveComponent[P, Px : PDS, c : Component] {
    c in P.components
    Px.components = P.components - c
} run RemoveComponent for 3

pred HighestVersionPolicy[P : PDS] {
    all s : Service, c : P.components, cx : c.(P.schedule)[s], cxx : P.components - cx {
        s in cxx.export && cxx.name = cx.name => cxx.version in ^prev[cx.version]
    }
} run HighestVersionPolicy for 3 but 1 PDS

fact SoundPDS {
    all P : PDS | {
        all c : P.components, s : Service | -- 1
            let cx = P.schedule[c, s] {
                (some cx iff s in c.import)     -- c and s require c' only iff c imports s
                &&
                (some cx => s in cx.export)  -- c and s require c' only if c' exports s
            }
        all c : P.components | c.(P.requires) = c.(P.schedule)[Service] -- 2
        // c requires precisely those components that schedule says c depends on for some service
    }
}

pred AGuidedSimulation[P, Px, Pxx : PDS, c1, c2 : Component] {
    AddComponent[P, Px, c1] RemoveComponent[P, Pxx, c2]
    HighestVersionPolicy[P] HighestVersionPolicy[Px] HighestVersionPolicy[Pxx]
} run AGuidedSimulation for 3

pred StructurallyEqual[P, Px : PDS] {
  P.components = Px.components
  P.schedule = Px.schedule
  P.requires = Px.requires
}

run StructurallyEqual for 2

assert AddingIsFunctionalForPDSs {
    all P, Px, Pxx : PDS, c : Component {
        AddComponent[P, Px, c] && AddComponent[P, Pxx, c] => StructurallyEqual[P, Px]
    }
} check AddingIsFunctionalForPDSs for 3