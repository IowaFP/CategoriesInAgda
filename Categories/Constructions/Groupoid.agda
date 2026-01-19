{-# OPTIONS --without-K #-}

module Categories.Constructions.Groupoid where 

open import Categories.Prelude
open import Categories.Category

-- ------------------------------------------------------------------------------
-- Groupoid categories are categories in which every morphism is an isomorphism.

module _ (𝒞 : Category o a e) where 
  open Category 𝒞
  open Isomorphism 𝒞

  record isGroupoid : Set (a ⊔ o ⊔ e) where 
    constructor Groupoid
    field 
      allIso : ∀ {A B : Obj} → (f : A ⇒ B) → isIso 𝒞 f 
  open isGroupoid public

record GroupoidCategory (o a e : Level) : Set (lsuc (o ⊔ a ⊔ e)) where 
    constructor _,_
    field 
        category : Category o a e
        groupoid : isGroupoid category

open GroupoidCategory public