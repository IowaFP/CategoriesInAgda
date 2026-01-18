{-# OPTIONS --without-K #-}

module Categories.NaturalTransformation.Base where 

open import Categories.Prelude
open import Categories.Category 
open import Categories.Functor 

open import Categories.Reasoning.Hom

--------------------------------------------------------------------------------
-- natural transformations

module _ {𝒞 : Category o₁ a₁ e₁} 
    {𝒟 : Category o₂ a₂ e₂}
    (F G : Functor 𝒞 𝒟) where 

  open Category
  private 
    module F = Functor F 
    module G = Functor G 

  record NaturalTransformation : Set (o₁ ⊔ a₁ ⊔ e₁ ⊔ o₂ ⊔ a₂ ⊔ e₂) where 
    constructor _,_

    field 
      η : ∀ {A : 𝒞 .Obj} → 𝒟 [ (F.₀ A) , (G.₀ A) ]
      naturality : ∀ {A B : 𝒞 .Obj} → (f : 𝒞 [ A , B ]) → 
                    𝒟 [ 𝒟 [ G.fmap f ∘ η ] ≈ 𝒟 [ η ∘ (F.fmap f) ] ]

  open NaturalTransformation public 
--------------------------------------------------------------------------------
-- Vertical composition of natural transformations

module _ {𝒞 : Category o₁ a₁ e₁} 
    {𝒟 : Category o₂ a₂ e₂}
    {F G H : Functor 𝒞 𝒟} where 
  open HomReasoning 𝒟
  private 
    module C = Category 𝒞 ; module D = Category 𝒟 
    module F = Functor F ; module G = Functor G ; module H = Functor H

  -- Vertical composition
  _∘V_ : NaturalTransformation G H → NaturalTransformation F G → NaturalTransformation F H 
  (η₁ , nat₁) ∘V (η₂ , nat₂) = (η₁ ∘ η₂) , λ f → 
    begin 
      H.fmap f ∘ (η₁ ∘ η₂) ≈⟨ assₗ ⟩ 
      H.fmap f ∘ η₁ ∘ η₂   ≈⟨ cong-∘ₗ (nat₁ f) ⟩ 
      η₁ ∘ G.fmap f ∘ η₂   ≈⟨ assᵣ ⟩ 
      η₁ ∘ (G.fmap f ∘ η₂) ≈⟨ cong-∘ᵣ (nat₂ f) ⟩ 
      η₁ ∘ (η₂ ∘ F.fmap f) ≈⟨ assₗ ⟩ 
      η₁ ∘ η₂ ∘ F.fmap f ∎
      where 
        open Category 𝒟

--------------------------------------------------------------------------------
-- Horizontal composition 

module _ {𝒞 : Category o₁ a₁ e₁} 
    {𝒟 : Category o₂ a₂ e₂}
    {ℰ : Category o₃ a₃ e₃}
    {F G : Functor 𝒞 𝒟}
    {J K : Functor 𝒟 ℰ} where
  private 
    module C = Category 𝒞 ; module D = Category 𝒟 ; module F = Functor F 
    module G = Functor G ; module J = Functor J ; module K = Functor K 
  open Category ℰ
  open HomReasoning ℰ

  -- Horizontal composition
  _∘H_ : NaturalTransformation J K → NaturalTransformation F G → NaturalTransformation (J ∘F F) (K ∘F G)
  (ε , nat₁) ∘H (η , nat₂) = (λ {A} → K.fmap η ∘ ε {F.₀ A}) , λ f →
    -- surely this proof could be simpler
    begin 
      K.fmap (G.fmap f) ∘ (K.fmap η ∘ ε)   ≈⟨ cong-∘ᵣ (nat₁ η) ⟩ 
      K.fmap (G.fmap f) ∘ (ε ∘ J.fmap η)   ≈⟨ assₗ ⟩
      K.fmap (G.fmap f) ∘ ε ∘ J.fmap η     ≈⟨ cong-∘ₗ (nat₁ (G.fmap f)) ⟩ 
      ε ∘ J.fmap (G.fmap f) ∘ J.fmap η     ≈⟨ assᵣ ⟩  
      ε ∘ (J.fmap (G.fmap f) ∘ J.fmap η)   ≈⟨ cong-∘ᵣ (sym-≈ (J.F-∘ η (G.fmap f))) ⟩  
      ε ∘ J.fmap (𝒟 [ G.fmap f ∘ η ])      ≈⟨ cong-∘ᵣ (J.F-cong (nat₂ f)) ⟩ 
      ε ∘ J.fmap (𝒟 [ η ∘ F.fmap f ])      ≈⟨ cong-∘ᵣ (J.F-∘ (F.fmap f) η) ⟩ 
      ε ∘ (J.fmap η ∘ J.fmap (F.fmap f))   ≈⟨ assₗ ⟩ 
      (ε ∘ J.fmap η) ∘ J.fmap (F.fmap f)   ≈⟨ sym-≈ (cong-∘ₗ (nat₁ η)) ⟩ 
      K.fmap η ∘ ε ∘ J.fmap (F.fmap f) ∎ 

