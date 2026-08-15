{-# OPTIONS --without-K #-}

module Categories.Category.Product where 

open import Categories.Prelude
open import Categories.Category.Base 
open import Categories.Category.Arrows
open import Categories.Functor.Base
open import Categories.NaturalTransformation
open import Categories.Reasoning.NaturalIsomorphism

--------------------------------------------------------------------------------
-- Product categories

module _ (𝒞 : Category o₁ a₁ e₁) (𝒟 : Category o₂ a₂ e₂) where
  open Category
  private 
    module C = Category 𝒞 ; module D = Category 𝒟
  _×_ : Category (o₁ ⊔ o₂) (a₁ ⊔ a₂) (e₁ ⊔ e₂)
  _×_  .Obj = 𝒞 .Obj * 𝒟 .Obj
  _×_ ._⇒_ (A , B) (C , D) = (𝒞 [ A , C ])  * (𝒟 [ B , D ])
  _×_ ._∘_ (f₁ , f₂) (g₁ , g₂) = (𝒞 [ f₁ ∘ g₁ ]) , (𝒟 [ f₂ ∘ g₂ ])
  _×_ .Id = (𝒞 .Id) , (𝒟 .Id) 
  _×_ ._≈_ (f₁ , f₂) (g₁ , g₂) = 𝒞 [ f₁ ≈ g₁ ] * 𝒟 [ f₂ ≈  g₂ ]
  _×_ .eqv .IsEquivalence.refl {f , g} = refl-≈ 𝒞 , refl-≈ 𝒟
  _×_ .eqv .IsEquivalence.sym (f , g) = sym-≈ 𝒞 f , sym-≈ 𝒟 g
  _×_ .eqv .IsEquivalence.trans (f₁ , g₁) (f₂ , g₂) = trans-≈ 𝒞 f₁ f₂ , trans-≈ 𝒟 g₁ g₂
  _×_ .idᵣ = 𝒞 .idᵣ , 𝒟 .idᵣ
  _×_ .idₗ = 𝒞 .idₗ , 𝒟 .idₗ
  _×_ .assₗ = 𝒞 .assₗ , 𝒟 .assₗ
  _×_ ._⋆_ {f = f₁ , f₂} {h₁ , h₂} {g₁ , g₂} {i₁ , i₂} (f₁≈h₁ , f₂≈h₂) (g₁≈i₁ , g₂≈i₂)  = 
    (f₁≈h₁ C.⋆ g₁≈i₁) , (f₂≈h₂ D.⋆ g₂≈i₂) 


--------------------------------------------------------------------------------
-- Canonical projections

module _ {𝒞 : Category o₁ a₁ e₁} {𝒟 : Category o₂ a₂ e₂} where
  open Functor 
  open Category 𝒞 ; open `Category 𝒟

  -- Projecting the left category out of a product category
  π¹ : (𝒞 × 𝒟) ⇛ 𝒞
  π¹ .F₀ = fst
  π¹ .fmap = fst
  π¹ .F-id = refl-≈
  π¹ .F-∘ _ _ = refl-≈
  π¹ .F-cong = fst 

  -- Projecting the right category
  π² : (𝒞 × 𝒟) ⇛ 𝒟 
  π² .F₀ = snd
  π² .fmap = snd
  π² .F-id = `refl-≈
  π² .F-∘ _ _ = `refl-≈
  π² .F-cong = snd 

------------------------------------------------------------------------------
-- Universal morphism

module _ {𝒞 : Category o₁ a₁ e₁} {𝒟 : Category o₂ a₂ e₂} {ℰ : Category o₃ a₃ e₃} where

  -- TODO:
  -- - Rephrase this as an instance of AdmitsProducts record.
  
  -- _×_ forms a product on the category of categories, where 
  -- ⟨ F , G ⟩ is the unique morphism such that 
  -- F ≃ π¹ ∘ ⟨ F , G ⟩ and G ≃  π² ∘ ⟨ F , G ⟩. 
  -- (See Categories.Instances.Cat)
  ⟨_,_⟩ : ∀ (F : 𝒞 ⇛ 𝒟) → (G : 𝒞 ⇛ ℰ) → 𝒞 ⇛ (𝒟 × ℰ)
  ⟨ F , G ⟩ = record
    { F₀         = < F₀ , G₀ >
    ; fmap       = < fmap , gmap > 
    ; F-id       = F-id , G-id
    ; F-∘        = λ f g → F-∘ f g , G-∘ f g
    ; F-cong     = < F-cong , G-cong > 
    }
    where 
      open Functor F ; open Gunctor G
  
  module _ (F : 𝒞 ⇛ 𝒟) (G : 𝒞 ⇛ ℰ) (H : 𝒞 ⇛ (𝒟 × ℰ)) where 
    open Functor F ; open Gunctor G ; open Hunctor H 
    
    -- ⟨ F , G ⟩ is unique w.r.t. to commutativity of product diagrams 
    ⟨⟩-unique : π¹ ∘F H ≃ₙ F → π² ∘F H ≃ₙ G → ⟨ F , G ⟩ ≃ₙ H
    ⟨⟩-unique π¹∘H π²∘H .nat .η = π¹∘H .iso .∼ , π²∘H .iso .∼
    ⟨⟩-unique π¹∘H π²∘H .nat .naturality f = η⁻¹-natural π¹∘H f , η⁻¹-natural π²∘H f
    ⟨⟩-unique π¹∘H π²∘H .iso .∼ = π¹∘H .nat .η , π²∘H .nat .η
    ⟨⟩-unique π¹∘H π²∘H .iso .iso = 
      (π¹∘H .iso .iso .rinv , π²∘H .iso .iso .rinv) , 
      (π¹∘H .iso .iso .linv , π²∘H .iso .iso .linv)
                