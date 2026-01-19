{-# OPTIONS --without-K #-}

module Categories.Constructions.Initial where 

open import Categories.Prelude
open import Categories.Category

-- ------------------------------------------------------------------------------
-- Initial Objects.
--
-- An object ⊥ is initial if there exists a (unique) morphism from ⊥ to 
-- every object A ∈ 𝒞.

module _ (𝒞 : Category o a e) where 
  open Category 𝒞
  open Isomorphism 𝒞

  record isInitial (⊥ : Obj)  : Set (a ⊔ o ⊔ e) where 
    constructor init

    Initial : Obj → Set (a ⊔ o)
    Initial A = ∀ (B : Obj) → A ⇒ B    

    field 
      ! : Initial ⊥
      unique : ∀ {A} (f : ⊥ ⇒ A) → f ≈ ! A 

    !-unique′ : ∀ {A} (f g : ⊥ ⇒ A) → f ≈ g 
    !-unique′ f g = trans-≈ (unique f) (sym-≈ (unique g)) 
    !-id : (f : ⊥ ⇒ ⊥) → f ≈ Id
    !-id f = !-unique′ f Id 
  
  -- An initial object is isomorphic to any other initial object in its category.
  ⊥-unique : {⊥₀ ⊥₁ : Obj} → isInitial ⊥₀ → isInitial ⊥₁ → ⊥₀ ≃ ⊥₁ 
  ⊥-unique {⊥₀} {⊥₁} ini₁@(init i₁ u₁) ini₂@(init i₂ u₂) = 
    i₁ ⊥₁ , i₂ ⊥₀ , !-id ini₂ (i₁ ⊥₁ ∘ i₂ ⊥₀) , !-id ini₁ (i₂ ⊥₀ ∘ i₁ ⊥₁)
    where open isInitial