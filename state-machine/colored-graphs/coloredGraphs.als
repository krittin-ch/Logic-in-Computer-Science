module ColoredGraphs

abstract sig Color {}

one sig Color1, Color2 extends Color {}

sig Node {
    color : Color
}

sig AboutColoredGraphs {
    nodes : set Node,
    edges : nodes -> nodes
} {
    edges = ~ edges 
    && all x : nodes, y : x.edges |
        not x.color = y.color
}

pred TwoColorable[g: AboutColoredGraphs] {
    // Ensure each node in the graph is colored with either Color1 or Color2
    all n: g.nodes | n.color in Color1 + Color2

    // Ensure the graph has at least 3 nodes
    && #g.nodes >= 3

    // Ensure each node has at least one outgoing edge
    && all n: g.nodes | some n.(g.edges)
    
    // Ensure each node has at least one incoming edge
    && all n: g.nodes | some { m: g.nodes | m -> n in g.edges }
}
run {
    some g : AboutColoredGraphs |
        TwoColorable[g]
} for 15 but 1 AboutColoredGraphs

// pred ThreeColorable[g : AboutColoredGraphs] {
//     all n : g.nodes |
//         # n.color = 3
//         # g.nodes >= 3
//     all x : g.nodes | some x.(g.edges) -- to see more interesting graphs
// } 

// run {
//     some g : AboutColoredGraphs |
//         ThreeColorable[g]
// } for 5 but 1 AboutColoredGraphs

// pred FourColorable[g : AboutColoredGraphs] {
//     all n : g.nodes |
//         # n.color = 4
//         # g.nodes >= 3
//     all x : g.nodes | some x.(g.edges) -- to see more interesting graphs
// } 

// run {
//     some g : AboutColoredGraphs |
//         FourColorable[g]
// } for 5 but 1 AboutColoredGraphs
