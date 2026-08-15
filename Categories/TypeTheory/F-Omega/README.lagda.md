# Categorical Semantics of System Fω

The interpretation of the STLC into CCCs can be generalized to **hyperdoctrines**, the seminal paper
on which is gyven by Seely. 

The core idea is to begin with a base Cartesian-closed category K of kinds.
- The kind ★ is interpreted as an object representing the category of types (or a universe of types 𝒰);
- The kind κ₁ `→ κ₂ is represented as the exponential object κ₂ ^ κ₁.

System F's universal quantification requires a **polymorphic product**,
which is right adjoint to the diagonal functor.

I'm not sure where to find more refined details outside of Seely's paper.
It's not clear to me how to generalize the denotation given into Set towards 
arbitrary categories. 

The interesting bit of this development would be that we could still 
represent substitutions and renamings functionally; unlike with dependent TT,
we do not need a category of contexts. 

I'm fairly certain this work is novel, insofar that, while denotations into Set of 
System F and Fω have been given by authors such as Saffrich et al and myself, I 
don't believe anyone has given a generalized categorical denotation. That is,
just as how the STLC denotation can be *instantiated* by arbitrary CCC (not just Set),
this denotation should be capable of other suitable instantiations.

A proper categorical treatment may also avoid the need for level stratification. 

## Works Cited 
- R. A. G. Seely, "Categorical semantics for higher order polymorphic lambda calculus", The Journal of Symbolic Logic 52(4), 1987.
- Hannes Saffrich, Peter Thiemann, Marius Weidner.
  Intrinsically Typed Syntax, a Logical Relation, and the Scourge of the Transfer Lemma. TyDe 2024
  - https://dl.acm.org/doi/10.1145/3678000.3678201