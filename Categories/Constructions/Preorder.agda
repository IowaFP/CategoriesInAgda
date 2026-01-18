{-# OPTIONS --without-K #-}

module Categories.Constructions.Preorder where 

open import Categories.Prelude
open import Categories.Category

-- ------------------------------------------------------------------------------
-- A preorder is a category in which all parallel arrows are equal.

module _ (𝒞 : Category o a e) where 
  open Category 𝒞
  open Isomorphism 𝒞

  record isPreorder : Set (a ⊔ o ⊔ e) where 
    constructor Preorder
    field 
       preorder : ∀ {A B : Obj} → (f g : A ⇒ B) → f ≈ g

record PreorderCategory : Set (lsuc (o ⊔ a ⊔ e)) where 
    field 
        category : Category o a e
        preorder : isPreorder category

open isPreorder public
open PreorderCategory public
