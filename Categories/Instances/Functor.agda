{-# OPTIONS --without-K #-}

module Categories.Instances.Functor where 

open import Categories.Prelude
open import Categories.Category 
open import Categories.Functor 
open import Categories.NaturalTransformation 
open import Categories.Category.Product
open import Categories.Instances.Setoid
open import Categories.Reasoning.Hom 
open import Categories.Category.Product 

--------------------------------------------------------------------------------
-- The Category of functors [𝒞 , 𝒟]

module _ (𝒞 : Category o₁ a₁ e₁) (𝒟 : Category o₂ a₂ e₂) where 
  open Category 𝒟 
  open HomReasoning 𝒟
  open _≃ₙ_

  [_,_] : Category _ _ _
  [_,_] .Obj = 𝒞 ⇛ 𝒟 
  [_,_] ._⇒_ = NaturalTransformation
  [_,_] ._∘_ {A = F} {G} {H} = _∘V_
  [_,_] .Id = IdN .nat 
  _≈_ [_,_] {A} {B} (η , nat-η) (ε , nat-ε) = ∀ {A : 𝒞 .Category.Obj} → η {A} ≈ ε {A} 
  [_,_] .eqv .IsEquivalence.refl = refl-≈ 
  [_,_] .eqv .IsEquivalence.sym x≈y {A} = x≈y ⁻¹
  [_,_] .eqv .IsEquivalence.trans x≈y y≈z {A} = x≈y ⨾ y≈z
  [_,_] ._⋆_ {f = f} {h} {g} {i} e₁ e₂ {A} =  e₁ ⋆ e₂
  [_,_] .idᵣ = idᵣ   
  [_,_] .idₗ = idₗ   
  [_,_] .assₗ = assₗ

module _ (𝒞 : Category o₁ a₁ e₁) (𝒟 : Category o₂ a₂ e₂) where 
  open HomReasoning 𝒞 
  open Category 𝒞 ; open `Category 𝒟 

  -- The "evaluation" functor, viewing [ 𝒟 , 𝒞 ] as an 
  -- exponential Dᶜ in the category 𝐂𝐚𝐭.                                         
  --        X × D                X
  --         |   \               |
  -- λg × id |    \ g            | λg
  --         v      v            v
  -- [D , C] × D --> C          [D , C] 
  --             eval

  evalF : ([ 𝒟 , 𝒞 ] × 𝒟) ⇛ 𝒞  
  evalF .Functor.F₀ (F , A) = F₀ A
    where open Functor F 
  evalF .Functor.fmap 
    {A = F , A} {B = G , B} ((η , naturality) , f) = gmap f ∘ η
    where open Gunctor G 
  evalF .Functor.F-id {F , A} = F-id ⋆ₗ Id ⨾ idₗ
    where open Functor F 
  evalF .Functor.F-∘ 
    {A = F , A} {B = G , B} {C = H , C} 
    ((η , nat-η) , f) ((ε , nat-ε) , g) = begin
      hmap (g `∘ f) ∘ (ε ∘ η)   ≈⟨ H-∘ f g ⋆ₗ (ε ∘ η) ⟩ 
      hmap g ∘ hmap f ∘ (ε ∘ η) ≈⟨ assₗ ⨾ assᵣ ⋆ₗ η ⟩ 
      hmap g ∘ (hmap f ∘ ε) ∘ η ≈⟨ hmap g ⋆ᵣ (nat-ε f) ⋆ₗ η ⟩ 
      hmap g ∘ (ε ∘ gmap f) ∘ η ≈⟨ assₗ ⋆ₗ η ⨾ assᵣ ⟩ 
      hmap g ∘ ε ∘ (gmap f ∘ η) ∎ 
    where open Functor F ; open Gunctor G ; open Hunctor H 
  evalF .Functor.F-cong 
    {F , A} {G , B} 
    {(η , nat-η) , f} {(ε , nat-ε) , g} 
    (η≈ε , f≈g) = (G-cong f≈g) ⋆ η≈ε       
    where open Gunctor G

  -- Currying
  λF[_] : ∀ {X : Category o₃ a₃ e₃} → 
           (X × 𝒟) ⇛ 𝒞 → 
           X ⇛ [ 𝒟 , 𝒞 ]
  λF[ g ] = {!   !} 
