{-# OPTIONS --without-K #-}

module Categories.Constructions.Discrete where 

open import Categories.Prelude
open import Categories.Category
open import Categories.Constructions.Groupoid
open import Categories.Constructions.Preorder

-- ------------------------------------------------------------------------------
-- A discrete category has only identities as morphisms.
-- 
{- A note on *weak* vs. *strict* categories: 

   We have no notion of object equivalence aside from isomorphism, hence a discrete 
   category may have nontrivial arrows between isomorphic objects. Consider a 
   category 𝒞 with two objects, A and B, with identity morphisms and arrows
   f : A → B and g : B → A s.t. f and g are isomorphic.
           f
        ------->
      A <------- B 
           g 
  This category is discrete because it is a preorder (all parallel arrows
  are equivalent) and a groupoid (all arrows are isomorphisms). But it has *more*
  than just identity arrows! This conflicts with a set-theoretic definition,
  where object equivalence is taken for granted. For example, wikipedia defines a 
  discrete category as one in which
  - Hom(X, X)  = {id}   for all objects X 
  - Hom(X , Y) = ∅      for all objects X ≠ Y
  further writing that | hom(X , Y) | = 1 when X ≠ Y. This definition
  is only true, in our case, when we take equality to mean isomorphism.


-}  

module _ (𝒞 : Category o a e) where 
  open Category 𝒞
  open Isomorphism 𝒞

  record isDiscrete : Set (a ⊔ o ⊔ e) where 
    constructor Discrete
    field 
      groupoid : isGroupoid 𝒞 
      preorder : isPreorder 𝒞

record DiscreteCategory : Set (lsuc (o ⊔ a ⊔ e)) where 
    field 
        category : Category o a e
        discrete : isDiscrete category
        
open isDiscrete public 
open DiscreteCategory public 
