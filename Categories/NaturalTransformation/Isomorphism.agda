{-# OPTIONS --without-K #-}

module Categories.NaturalTransformation.Isomorphism where 

open import Categories.Prelude
open import Categories.Category 
open import Categories.Functor.Base  
open import Categories.NaturalTransformation.Base
open import Categories.Reasoning.Hom

--------------------------------------------------------------------------------
-- natural transformations

module _ {𝒞 : Category o₁ a₁ e₁} 
    {𝒟 : Category o₂ a₂ e₂}
    (F G : Functor 𝒞 𝒟) where 

  open Category 𝒞
  open Functor F ; open Gunctor G 

  infixr 1 _≃ₙ_
  -- Natural isomorphisms
  record _≃ₙ_ : Set (o₁ ⊔ a₁ ⊔ e₁ ⊔ o₂ ⊔ a₂ ⊔ e₂) where 
    constructor _,_    
    open NaturalTransformation
    field 
      nat : NaturalTransformation F G 
      iso : ∀ {A : Obj} → isIso 𝒟 (nat .η {A})
  open _≃ₙ_ public 

--------------------------------------------------------------------------------
-- Natural isomorphisms form an equivalence relation on functors

module _ 
    {𝒞 : Category o₁ a₁ e₁} 
    {𝒟 : Category o₂ a₂ e₂} where 

  open HomReasoning 𝒟 
  open Category 𝒟
  open isIso 
  open areInverse 

  -- the identity natural isomorphism
  IdN : ∀ {F : Functor 𝒞 𝒟} → F ≃ₙ F
  IdN {F} = (Id , λ f → begin 
    fmap f ∘ Id ≈⟨ idᵣ ⟩ 
    fmap f      ≈⟨ idₗ ⁻¹ ⟩ 
    Id ∘ fmap f ∎) ,
    Id , idₗ , idₗ
    where 
      open Functor F 
  

  -- By definition, η : F → G is a natural isomorphism if each arrow 
  --   η(A) : F A ⇒ G A  
  -- is an isomorphism. Observe that we do not stipulate the condition
  -- that each the natural transformation induced as the inverse of η
  -- is indeed natural. We prove here that is unnecessary to do so:
  -- we can show directly that η⁻¹ is natural.
  η⁻¹-natural : ∀ {F G : Functor 𝒞 𝒟} (γ : F ≃ₙ G) → 
                  Natural G F (λ {A : 𝒞 .Category.Obj} → γ .iso {A} .∼)
  η⁻¹-natural {F = F} {G} ((η , nat) , γ) f = 
    let η⁻¹ : ∀ {A} → G₀ A ⇒ F₀ A   
        η⁻¹ = λ {A} → ∼ (γ {A})
        η-linv = γ .iso .linv
        η-rinv = γ .iso .rinv in 
      begin 
        fmap f ∘ η⁻¹              ≈⟨ (sym-≈ idₗ) ⋆ₗ η⁻¹ ⟩ 
        Id ∘ fmap f ∘ η⁻¹         ≈⟨ ((η-rinv ⁻¹) ⋆ₗ fmap f) ⋆ₗ η⁻¹ ⟩ 
        η⁻¹ ∘ η ∘ fmap f ∘ η⁻¹   ≈⟨ assᵣ ⋆ₗ η⁻¹ ⟩ 
        η⁻¹ ∘ (η ∘ fmap f) ∘ η⁻¹ ≈⟨ (η⁻¹ ⋆ᵣ (sym-≈ (nat f))) ⋆ₗ η⁻¹ ⟩ 
        η⁻¹ ∘ (gmap f ∘ η) ∘ η⁻¹ ≈⟨ ((assₗ ⋆ₗ η⁻¹) ⨾ assᵣ) ⟩ 
        η⁻¹ ∘ gmap f ∘ (η ∘ η⁻¹) ≈⟨ (((η⁻¹ ∘ gmap f) ⋆ᵣ η-linv) ⨾ idᵣ) ⟩ 
        η⁻¹ ∘ gmap f ∎
      where 
        open Functor F ; open Gunctor G 

  --------------------------------------------------------------------------------
  -- Natural isomorphisms form an equivalence relation on functors

  refl-≃ₙ = IdN 

  sym-≃ₙ : ∀ {F G : Functor 𝒞 𝒟} → F ≃ₙ G → G ≃ₙ F 
  sym-≃ₙ {F} {G} ((η , nat) , γ) = 
    ((λ {A} → ∼ γ) , η⁻¹-natural {F} {G} ((η , nat) , γ)) , 
      λ {A} → η , γ .iso .rinv , γ  .iso .linv

  trans-≃ₙ : ∀ {F G H : Functor 𝒞 𝒟} → F ≃ₙ G → G ≃ₙ H → F ≃ₙ H
  trans-≃ₙ {F} {G} {H} ((η , nat-η) , γ₁) ((ε , nat-ε) , γ₂) = 
    ((λ {A} →  ε ∘ η) , λ f →    
      begin
        hmap f ∘ (ε ∘ η)   ≈⟨ assₗ ⨾ (nat-ε f) ⋆ₗ η ⟩ 
        ε ∘ gmap f ∘ η     ≈⟨ assᵣ ⨾ ε ⋆ᵣ (nat-η f) ⨾ assₗ ⟩ 
        ε ∘ η ∘ fmap f ∎) , 
    λ {A} → ∼ γ₁ ∘ ∼ γ₂ , 
      (begin 
        ε ∘ η ∘ (∼ γ₁ ∘ ∼ γ₂)  ≈⟨ (assₗ ⨾ assᵣ ⋆ₗ ∼ γ₂ ⨾ (ε ⋆ᵣ (γ₁ .iso .linv)) ⋆ₗ ∼ γ₂) ⟩ 
        ε ∘ Id ∘ ∼ γ₂          ≈⟨ (assᵣ ⨾ ε ⋆ᵣ idₗ) ⟩ 
        ε ∘ ∼ γ₂               ≈⟨ γ₂ .iso .linv ⟩ 
        Id ∎)  , 
      (begin
        ∼ γ₁ ∘ ∼ γ₂ ∘ (ε ∘ η)  ≈⟨ (assₗ ⨾ (assᵣ ⋆ₗ η ⨾ (∼ γ₁ ⋆ᵣ (γ₂ .iso .rinv)) ⋆ₗ η)) ⟩ 
        ∼ γ₁ ∘ Id ∘ η          ≈⟨ idᵣ ⋆ₗ η ⟩
        ∼ γ₁ ∘ η               ≈⟨ γ₁ .iso .rinv ⟩ 
        Id ∎)
    where 
      open Functor F ; open Gunctor G ; open Hunctor H 
 
  nat-setoid : Setoid _ _
  nat-setoid = record
    { Carrier       = Functor 𝒞 𝒟 
    ; _≈_           = _≃ₙ_
    ; isEquivalence = record { refl = refl-≃ₙ ; sym = sym-≃ₙ ; trans = trans-≃ₙ }
    }


--------------------------------------------------------------------------------
-- The category of categories has functors as arrows and setoid equivalence 
-- given by natural isomorphism: that functor composition respect setoid 
-- equivalence is given precisely by horizontal composition of natural 
-- isomorphisms. We also prove the other laws (composition by the identity 
-- functor is an identity, and associativity.)

module _ {𝒞 : Category o₁ a₁ e₁} 
    {𝒟 : Category o₂ a₂ e₂}
    {ℰ : Category o₃ a₃ e₃}
    {F G : Functor 𝒞 𝒟}
    {J K : Functor 𝒟 ℰ} where
  open Category ℰ ; open `Category 𝒟 
  open Functor F ; open Gunctor G 
  open Junctor J ; open Kunctor K 
  open _≃ₙ_ ; open NaturalTransformation 
  open isIso ; open areInverse 
  open HomReasoning ℰ 
    
  -- Horizontal composition of natural isomorphisms yields 
  -- a natural isomorphism. ­
  H-iso : F ≃ₙ G → J ≃ₙ K → (J ∘F F) ≃ₙ (K ∘F G)
  H-iso (η₁@(μ , nat₁) , γ₁) (η₂@(ε , nat₂) , γ₂) = 
    let ((α , nat-α) , γ-α) = α in 
    let ((β , nat-β) , γ-β) = β in
    (η₂ ∘H η₁) , 
    λ {A} → ζ .η , 
      (begin 
        kmap μ ∘ ε ∘ (jmap α ∘ β) ≈⟨ ((nat₂ μ) ⋆ₗ (jmap α ∘ β) ⨾ assₗ) ⟩ 
        ε ∘ jmap μ ∘ jmap α ∘ β   ≈⟨ (assᵣ ⨾ ε ⋆ᵣ ((J-∘ α μ) ⁻¹)) ⋆ₗ β ⟩ 
        ε ∘ jmap (μ `∘ α) ∘ β     ≈⟨ (ε ⋆ᵣ J-cong (γ₁ .iso .linv)) ⋆ₗ β ⨾ ((ε ⋆ᵣ J-id) ⋆ₗ β) ⟩  -- (? ⋆ᵣ ((J-cong (γ₁ .iso .linv)) ⋆ₗ ? ⨾ ?))
        ε ∘ Id ∘ β                ≈⟨ (idᵣ ⋆ₗ β ⨾ γ₂ .iso .linv) ⟩ 
        Id ∎) ,  
      (begin 
        jmap α ∘ β ∘ (kmap μ ∘ ε) ≈⟨ ((nat-β α) ⋆ₗ (kmap μ ∘ ε) ⨾ assₗ) ⟩ 
        β ∘ kmap α ∘ kmap μ ∘ ε   ≈⟨ (assᵣ ⨾ β ⋆ᵣ ((K-∘ μ α) ⁻¹)) ⋆ₗ ε ⟩ 
        β ∘ kmap (α `∘ μ) ∘ ε      ≈⟨ β ⋆ᵣ ((K-cong (γ-α .iso .linv)) ⨾ K-id) ⋆ₗ ε ⟩ 
        β ∘ Id ∘ ε                    ≈⟨ (idᵣ ⋆ₗ ε ⨾ γ₂ .iso .rinv) ⟩
        Id ∎)
    where 
      α : G ≃ₙ F
      α = sym-≃ₙ (η₁ , γ₁)
      β : K ≃ₙ J 
      β = sym-≃ₙ (η₂ , γ₂)
      ζ : NaturalTransformation (K ∘F G) (J ∘F F) 
      ζ = (β .nat) ∘H (α .nat)

module _ {𝒞 : Category o₁ a₁ e₁} 
    {𝒟 : Category o₂ a₂ e₂}
    {F : Functor 𝒞 𝒟} where
  open `Category 𝒞 ; open Category 𝒟 
  open Functor F 

  

  IdF-idₗ : (IdF ∘F F) ≃ₙ F 
  IdF-idₗ = 
    (Id , λ f → idᵣ ⨾ idₗ ⁻¹) , 
    Id , idₗ , idₗ

  IdF-idᵣ : (F ∘F IdF) ≃ₙ F 
  IdF-idᵣ = 
    (Id , λ f → idᵣ ⨾ idₗ ⁻¹) , 
    Id , idₗ , idₗ

module _ 
    {𝒜 : Category o a e}
    {ℬ : Category o₁ a₁ e₁} 
    {𝒞 : Category o₂ a₂ e₂}
    {𝒟 : Category o₃ a₃ e₃}
    (F : Functor 𝒜 ℬ)
    (G : Functor ℬ 𝒞)
    (H : Functor 𝒞 𝒟) where
  open Category 𝒟 
  Functor-assₗ : H ∘F (G ∘F F) ≃ₙ (H ∘F G) ∘F F 
  Functor-assₗ = (Id , λ f → idᵣ ⨾ idₗ ⁻¹) , Id , idᵣ , idᵣ
