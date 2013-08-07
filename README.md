Zebra.js was an exploration in Constraint Programming.

Information on the Zebra Puzzle can be found at: http://en.wikipedia.org/wiki/Zebra_puzzle

Special thanks to Willem-Jan van Hoeve and Irit Katriel at Carnegie Mellon for their enlightening research on meta-problem analysis of global constraints.

This particular family-friendly incarnation was derived from the writings of Russel and Norvig, Artificial Intelligence: A Modern Approach.

Given a set of variables (people, pets, drinks, etc...), a block of houses, and a set of constraints on who or what may reside in which house, the point of the puzzle is to determine a valid assignment which satisfies all of the given constraints.  A typical objective is to state which person owns the zebra, hence the name of the puzzle.

The CSP began as a simple adjacency list of arrays, which represented the domain of the variables.  A very simple checking algorithm allowed me to reduce from the domain of the variables those values which were known to be in conflict.  I used a first-solution-halting backtrack flavored tree search, initially using a vanilla AC1 algorithm.  This turne d into the pseudo-AC3 algorithm.  The gains prompted me to research CSP in more detail.

After spending several days surveying Constraint Programming in general I began to write this little framework.  I chose JavaScript almost tongue in cheek as I had previously only encountered Constraint Programming in lower-level or compiled languages.  I also wanted the solution to be browser compatible and I wanted an excuse to use underscore.js, a framework which makes JavaScript feel a bit more functional in nature.

Days turned to into weeks as I began pouring over research in Constraint Programming and optimization.  Although I wished to maintain the simple object-oriented nature and the slightly inefficient list-comprehension style programming, I decided to incorporate both extensibility and expressiveness into the framework.  Constraints are constructed via closure in a very intuitive way which allows two hook points, one for inference and another for an optional domain pruning function.

The Constraint Graph is represented as a (sometimes) directed acyclic hypergraph.  I use a Bipartite Flow graph representation to incorporate graph-theoretic solutions to the Global ALL_DIFF constraint, allowing me to perform arbitrarily strong consistency without resorting to an arity decomposition.  The solutions are a conditional combination of Flow Theory, Matching Theory and a convenient theorem involving Strongly Connected Components of graphs.

While at first dishearteningly slow, a series of [still-incomplete] optimizations to the code reduced the runtime from >22 seconds to <235 ms.  This experiment strenghtened my belief that Artificial Intelligence as a science can be taught seriously and interactively via the browser.

