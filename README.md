# Coxeter Groups in Lean

We formalize in Lean some results on Coxeter groups, following the textbooks [[1]](#ref1) and [[2]](#ref2). The results are organized as follows:

* [Basic.lean](Coxeter/Basic.lean)
    * Basic definitions and lemmas
* [Opposite.lean](Coxeter/Opposite.lean)
    * The opposite of a Coxeter group
* [PermutationRepresentation.lean](Coxeter/PermutationRepresentation.lean)
    * Construction of the permutation repersentation
* [StrongExchange.lean](Coxeter/StrongExchange.lean)
    * Strong exchange
    * Deletion property
* [Bruhat.lean](Coxeter/Bruhat.lean)
    * Definition of the Bruhat order
    * Subword property
    * Lifting property
    * The longest element of a finite Coxeter group
* [GeometricRepresentation.lean](Coxeter/GeometricRepresentation.lean)
    * Construction of the geometric repersentation

## References

<a name="ref1">[1]</a>: A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*. Springer, 2005. DOI: [10.1007/3-540-27596-7](https://doi.org/10.1007/3-540-27596-7)

<a name="ref2">[2]</a>: N. Bourbaki, *Groupes et algèbres de Lie*. Springer, 2007. DOI: [10.1007/978-3-540-34491-9](https://doi.org/10.1007/978-3-540-34491-9)
