
# Fundamentos de la Computación in Liquid Haskell

An implementation of the "Fundamentos de la Computación" course
at Universidad ORT, with proofs developed in Liquid Haskell following
a paper and pencil style whenever possible. 

The course serves as an introduction to:

- Lambda calculus and functional programming, using Haskell on the practical side.
- Recursion as a definition method and Induction as a proof method.

The module hierarchy follows the course natural progression:

1. `Bool.hs`: Implementation of boolean values with proofs.
2. `Nat.hs`: Implementation of natural numbers in Peano style with proofs.
3. `List.hs`: Implementation of generic lists in cons style with proofs.
3. `AB.hs`: Implementation of generic binary trees with proofs.

In this course, the approach to verification is *external*. This means, we first write pure functional programs and then write proofs of properties about them. So, the proofs may be considered separate external artifacts. Originally, proofs were only possible on paper and pencil, but Liquid Haskell makes their mechanization possible.
However, note that using Liquid Haskell an *internal* approach is also possible
because properties can be expressed more directly via refinement types on
the program itself.

The course doesn't make much emphasis on proving termination. 
Consequently, termination checking is turned off in LH.


## TODO

- Implement polymorphic equality/inequality operators using type classes.
  So we don't need to rewrite some functions (e.g `elemB` and `elemN`) for different types.
- Prove `<=` is correct with respect to a mathematical definition.
- Implement other kinds of trees.
- Experiment with PLE, the automation tactic provided by LH. Some proofs could be
  written again using less steps.