{-# OPTIONS --without-K #-}

module Categories.NaturalTransformation.Base where 

open import Categories.Prelude
open import Categories.Category 
open import Categories.Functor.Base 

open import Categories.Reasoning.Hom

--------------------------------------------------------------------------------
-- natural transformations

module _ {𝒞 : Category o₁ a₁ e₁} 
    {𝒟 : Category o₂ a₂ e₂}
    (F G : 𝒞 ⇛ 𝒟) where 

  open Category 𝒞 ; open `Category 𝒟
  open Functor F ; open Gunctor G 
  
  Natural : (η : ∀ {A : Obj} → F₀ A `⇒ G₀ A) → Set _ 
  Natural η = ∀ {A B : Obj} → (f : A ⇒ B) → 
                gmap f `∘ η `≈ η `∘ (fmap f)

  record NaturalTransformation : Set (o₁ ⊔ a₁ ⊔ e₁ ⊔ o₂ ⊔ a₂ ⊔ e₂) where 
    constructor _,_

    field 
      η : ∀ {A : Obj} → F₀ A `⇒ G₀ A
      naturality : Natural η

  -- Infix notation for natural transformations
  infixr 7 _⇒ₙ_
  _⇒ₙ_ = NaturalTransformation

  open NaturalTransformation public 
--------------------------------------------------------------------------------
-- Vertical composition of natural transformations

module _ {𝒞 : Category o₁ a₁ e₁} 
    {𝒟 : Category o₂ a₂ e₂}
    {F G H : 𝒞 ⇛ 𝒟} where 
  open HomReasoning 𝒟
  open Functor F ; open Gunctor G ; open Hunctor H
  private 
    module C = Category 𝒞 ; module D = Category 𝒟 
    

  -- Vertical composition
  _∘V_ : G ⇒ₙ H → F ⇒ₙ G → F ⇒ₙ H 
  (η₁ , nat₁) ∘V (η₂ , nat₂) = (η₁ ∘ η₂) , λ f → 
    begin 
      hmap f ∘ (η₁ ∘ η₂) ≈⟨ assₗ ⟩ 
      hmap f ∘ η₁ ∘ η₂   ≈⟨ (nat₁ f) ⋆ₗ η₂  ⟩ 
      η₁ ∘ gmap f ∘ η₂   ≈⟨ assᵣ ⟩ 
      η₁ ∘ (gmap f ∘ η₂) ≈⟨ η₁ ⋆ᵣ (nat₂ f) ⟩ 
      η₁ ∘ (η₂ ∘ fmap f) ≈⟨ assₗ ⟩ 
      η₁ ∘ η₂ ∘ fmap f ∎
      where 
        open Category 𝒟

--------------------------------------------------------------------------------
-- Horizontal composition 

module _ {𝒞 : Category o₁ a₁ e₁} 
    {𝒟 : Category o₂ a₂ e₂}
    {ℰ : Category o₃ a₃ e₃}
    {F G : 𝒞 ⇛ 𝒟}
    {J K : 𝒟 ⇛ ℰ} where
  open Functor F ; open Gunctor G
  open Junctor J ; open Kunctor K    
  open Category ℰ ; open `Category 𝒟
    
  open HomReasoning ℰ

  -- Horizontal composition
  _∘H_ : J ⇒ₙ K → F ⇒ₙ G → (J ∘F F) ⇒ₙ (K ∘F G)
  (ε , nat₁) ∘H (η , nat₂) = (λ {A} → kmap η ∘ ε {F₀ A}) , λ f →
    -- surely this proof could be simpler
    begin 
      kmap (gmap f) ∘ (kmap η ∘ ε)   ≈⟨ kmap (gmap f) ⋆ᵣ (nat₁ η) ⟩ 
      kmap (gmap f) ∘ (ε ∘ jmap η)   ≈⟨ assₗ ⟩
      kmap (gmap f) ∘ ε ∘ jmap η     ≈⟨ (nat₁ (gmap f)) ⋆ₗ jmap η ⟩ 
      ε ∘ jmap (gmap f) ∘ jmap η     ≈⟨ assᵣ ⟩  
      ε ∘ (jmap (gmap f) ∘ jmap η)   ≈⟨ ε ⋆ᵣ ((J-∘ η (gmap f)) ⁻¹) ⟩  
      ε ∘ jmap (gmap f `∘ η)      ≈⟨ ε ⋆ᵣ (J-cong (nat₂ f)) ⟩ 
      ε ∘ jmap (η `∘ fmap f)      ≈⟨ ε ⋆ᵣ (J-∘ (fmap f) η) ⟩ 
      ε ∘ (jmap η ∘ jmap (fmap f))   ≈⟨ assₗ ⟩ 
      (ε ∘ jmap η) ∘ jmap (fmap f)   ≈⟨ ((nat₁ η) ⋆ₗ jmap (fmap f)) ⁻¹ ⟩ 
      kmap η ∘ ε ∘ jmap (fmap f) ∎ 

--------------------------------------------------------------------------------
-- Natural transformations F ⇒ₙ G form a setoid
-- 
-- where two natural transformations are deemed equivalent if they are 
-- extensionally equivalent w.r.t. the underlying category's setoid on arrows.
module _ {𝒞 : Category o₁ a₁ e₁} 
    {𝒟 : Category o₂ a₂ e₂}
    (F G : 𝒞 ⇛ 𝒟) where

  open Category 𝒟
  nat-setoid : Setoid _ _ 
  nat-setoid .Setoid.Carrier = F ⇒ₙ G
  nat-setoid .Setoid._≈_ (η , _) (ε , _) = ∀ {A} → η {A} ≈ ε {A} 
  nat-setoid .Setoid.isEquivalence .IsEquivalence.refl = refl-≈
  nat-setoid .Setoid.isEquivalence .IsEquivalence.sym f {A} = sym-≈ (f {A})
  nat-setoid .Setoid.isEquivalence .IsEquivalence.trans f g {A} = trans-≈ (f {A}) (g {A}) 
