A small CSP Solver written in JavaScript (circa 2013) as an exploration in [Constraint Programming](https://en.wikipedia.org/wiki/Constraint_programming)


# Overview / Strategy

After spending several days surveying Constraint Programming in general I began to write this little framework.  I chose JavaScript almost tongue in cheek as I had previously only encountered Constraint Programming in lower-level or compiled languages.  One of *my* constraints was browser compatibility for presentation purposes.

Constraints are simple predicate functions.


## Naive Approach

The CSP began as a simple adjacency list of arrays, which represented the domain of the variables.  A very simple checking algorithm allowed me to reduce from the domain of the variables those values which were known to be in conflict.  I used a first-solution-halting backtrack flavored tree search, initially using a vanilla AC1 algorithm.  This turn d into the pseudo-AC3 algorithm.  The gains prompted me to research CSP in more detail.


## Optimizations

Days turned to into weeks as I began pouring over research in Constraint Programming and optimization.

The Constraint Graph is represented as a (sometimes) directed acyclic hypergraph.  I use a Bipartite Flow graph representation to incorporate graph-theoretic solutions to the Global ALL<sub>DIFF</sub> constraint, allowing me to perform arbitrarily strong consistency without resorting to an arity decomposition.

The optimizations involve elements of Flow Theory, Matching Theory and a convenient theorem involving Strongly Connected Components of graphs that feels like magic.

The *code itself* is not optimized, but written in an intuitive object-oriented style.


# Example: Zebra Puzzle

The [Zebra Puzzle](http://en.wikipedia.org/wiki/Zebra_puzzle) is a toy logic puzzle used for fun and to test AI algorithms. 

This particular family-friendly incarnation was derived from the writings of Russel and Norvig, Artificial Intelligence: A Modern Approach.

Given a set of variables (people, pets, drinks, etc&#x2026;), a block of houses, and a set of constraints on who or what may reside in which house, the point of the puzzle is to determine a valid assignment which satisfies all of the given constraints.  A typical objective is to state which person owns the zebra, hence the name of the puzzle.


## Constraints

1.  The Englishman lives in the red house.
2.  The Spaniard owns the dog.
3.  The Norwegian lives in the first house on the left.
4.  The green house is immediately to the right of the ivory house.
5.  The man who eats Hershey bars lives in the house next to the man with the fox.
6.  Kit Kats are eaten in the yellow house.
7.  The Norwegian lives next to the blue house.
8.  The Smarties eater owns snails.
9.  The Snickers eater drinks orange juice.
10. The Ukrainian drinks tea.
11. The Japanese eats Milky Ways.
12. Kit Kats are eaten in a house next to the house where the horse is kept.
13. Coffee is drunk in the green house.
14. Milk is drunk in the middle house.


## Solution

<table border="2" cellspacing="0" cellpadding="6" rules="groups" frame="hsides">


<colgroup>
<col  class="org-left" />
</colgroup>

<colgroup>
<col  class="org-left" />

<col  class="org-left" />

<col  class="org-left" />

<col  class="org-left" />

<col  class="org-left" />
</colgroup>
<tbody>
<tr>
<td class="org-left">House</td>
<td class="org-left">1</td>
<td class="org-left">2</td>
<td class="org-left">3</td>
<td class="org-left">4</td>
<td class="org-left">5</td>
</tr>


<tr>
<td class="org-left">Color</td>
<td class="org-left">yellow</td>
<td class="org-left">blue</td>
<td class="org-left">red</td>
<td class="org-left">ivory</td>
<td class="org-left">green</td>
</tr>


<tr>
<td class="org-left">Nationality</td>
<td class="org-left">Norwegian</td>
<td class="org-left">Ukrainian</td>
<td class="org-left">Englishman</td>
<td class="org-left">Spaniard</td>
<td class="org-left">Japanese</td>
</tr>


<tr>
<td class="org-left">Drinks</td>
<td class="org-left">water</td>
<td class="org-left">tea</td>
<td class="org-left">milk</td>
<td class="org-left">OJ</td>
<td class="org-left">coffee</td>
</tr>


<tr>
<td class="org-left">Pet</td>
<td class="org-left">fox</td>
<td class="org-left">horse</td>
<td class="org-left">snail</td>
<td class="org-left">dog</td>
<td class="org-left">zebra</td>
</tr>


<tr>
<td class="org-left">Eats</td>
<td class="org-left">kit-kat</td>
<td class="org-left">hershey</td>
<td class="org-left">smarties</td>
<td class="org-left">snickers</td>
<td class="org-left">milkey-way</td>
</tr>
</tbody>
</table>


## Results

<table border="2" cellspacing="0" cellpadding="6" rules="groups" frame="hsides">


<colgroup>
<col  class="org-left" />

<col  class="org-left" />
</colgroup>
<thead>
<tr>
<th scope="col" class="org-left">Method</th>
<th scope="col" class="org-left">Time</th>
</tr>
</thead>

<tbody>
<tr>
<td class="org-left">Naive Solution (2013)</td>
<td class="org-left">22 <b>seconds</b></td>
</tr>


<tr>
<td class="org-left">Optimized (2013)</td>
<td class="org-left">235 ms</td>
</tr>


<tr>
<td class="org-left">Optimized (2023)</td>
<td class="org-left">38 ms</td>
</tr>
</tbody>
</table>


# Installation & Usage

    npm install
    node zebra.js

**Dependencies**

-   NodeJS
-   Underscore.js


# Acknowledgments

Special thanks to Willem-Jan van Hoeve and Irit Katriel at Carnegie Mellon for their enlightening research on meta-problem analysis of global constraints.

Van Hoeve, W.-J., & Katriel, I. (2006). Global Constraints. In Handbook of Constraint Programming (pp. 169-203). ISBN 9780080463803. Retrieved from [<https://www.andrew.cmu.edu/user/vanhoeve/papers/chapter.pdf>]

Russell, S. J. 1., Norvig, P., & Davis, E. (2010). Artificial intelligence: a modern approach. 3rd ed. Upper Saddle River, NJ, Prentice Hall.


# License

The solver and puzzle are MIT licensed

