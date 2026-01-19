{-# OPTIONS --without-K #-}

module Categories.Constructions.Terminal where 

open import Categories.Prelude
open import Categories.Category
open import Categories.Constructions.Initial

-- ------------------------------------------------------------------------------
-- Terminal Objects.
--
-- Dual to initial objects, An object ⊤ is terminal if there exists a 
-- (unique) morphism from A to ⊤ for every object A ∈ 𝒞.

module _ (𝒞 : Category o a e) where 
  open Category 𝒞
  open Isomorphism 𝒞

  record isTerminal (⊤ : Obj) : Set (a ⊔ o ⊔ e) where 
    constructor term

    Terminal : Obj → Set (a ⊔ o)
    Terminal B = ∀ (A : Obj) → A ⇒ B    

    field
      ! : Terminal ⊤
      unique : ∀ {A : Obj} → (f : A ⇒ ⊤) → f ≈ ! A

    !-unique′ : ∀ {A} (f g : A ⇒ ⊤) → f ≈ g 
    !-unique′ f g = trans-≈ (unique f) (sym-≈ (unique g)) 
    !-id : (f : ⊤ ⇒ ⊤) → f ≈ Id
    !-id f = !-unique′ f Id     

  ⊤-unique : {⊤₀ ⊤₁ : Obj} → isTerminal ⊤₀ → isTerminal ⊤₁ → ⊤₀ ≃ ⊤₁
  ⊤-unique {⊤₀} {⊤₁} term₁@(term i₁ u₁) term₂@(term i₂ u₂) = 
    i₂ ⊤₀ , i₁ ⊤₁ , !-id term₂ (i₂ ⊤₀ ∘ i₁ ⊤₁) , !-id term₁ (i₁ ⊤₁ ∘ i₂ ⊤₀)
    where open isTerminal

-- ------------------------------------------------------------------------------
-- initial and terminal objects are dual

module _ (𝒞 : Category o a e) where 
  open Category 𝒞 
  private 
    𝒞ᵒᵖ = op 

  ⊥-dual-⊤ : {⊥ : Obj} → isInitial 𝒞 ⊥ → isTerminal 𝒞ᵒᵖ ⊥ 
  ⊥-dual-⊤ {⊥} i@(init ! unique) = term ! unique 


  ⊤-dual-⊥ : {⊤ : Obj} → isTerminal 𝒞 ⊤ → isInitial 𝒞ᵒᵖ ⊤ 
  ⊤-dual-⊥ {⊤} t@(term ! unique) = init ! unique 