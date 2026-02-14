# Ch4 Sets and Functions
1. In type theory, a property or predicate on a type `α` is just a function `P : α → Prop`
2. In fact, set-builder notation is used to define
    `s ∩ t` as `{x | x ∈ s ∧ x ∈ t}`
    `s ∪ t` as `{x | x ∈ s ∨ x ∈ t}`
    `∅` as `{x | False}`
    `univ` as `{x | True}`

# Ch7 Structures
## 7.2 Algebraic structures
1. A **partially ordered set** consists of a set P and a binary relation `<=` on P that is **transitive and reflexive**
2. A **group** consists of a set G with 
    an **associative** binary operation
    an **identity element 1**
    a function $g \rightarrow g^{-1}$ that returns an inverse for each g in G 
    A group is abelian or commutative if the operation is **commutative**
3. A **lattice** is a partially ordered set with meets and joins
4. A **ring** consists of an (additively written) **abelian group** $(R, +, 0, x \rightarrow -x)$ together with an associative multiplication operation `·` and an identity `1`, such that multiplication distributes over addition. A ring is commutative if the multiplication is commutative.
5. An **ordered ring**
6. A **metric space** consists of a set X and a function $d: X \times X \rightarrow \R$  such that the following hold:
    d(x, y) >= 0 for every x and y in X
    d(x, y) = 0 iff x = y
    d(x, y) = d(y, x) for every x and y in X
    d(x, z) <= d(x, y) + d(y, z) for every x, y and z in X
7. A **topological space** 