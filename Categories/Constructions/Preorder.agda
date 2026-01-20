{-# OPTIONS --without-K #-}

module Categories.Constructions.Preorder where 

open import Categories.Prelude
open import Categories.Category

-- ------------------------------------------------------------------------------
-- A preorder is a category in which all parallel arrows are equal.

module _ (𝒞 : Category o a e) where 
  open Category 𝒞
  open Isomorphism 𝒞

  isPreorder : Set (a ⊔ o ⊔ e)
  isPreorder = ∀ {A B : Obj} → (f g : A ⇒ B) → f ≈ g

record PreorderCategory o a e : Set (lsuc (o ⊔ a ⊔ e)) where 
    field 
        category : Category o a e
        preorder : isPreorder category

open PreorderCategory public
