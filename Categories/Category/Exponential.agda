{-# OPTIONS --without-K #-}

module Categories.Category.Exponential where 

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
  [_,_] ._⇒_ = _⇒ₙ_
  [_,_] ._∘_ {A = F} {G} {H} = _∘V_
  [_,_] .Id = IdN .nat 
  [_,_] ._≈_ {F} {G} = nat-setoid F G .Setoid._≈_
  [_,_] .eqv {F} {G} = nat-setoid F G .Setoid.isEquivalence
  [_,_] ._⋆_ {f = f} {h} {g} {i} e₁ e₂ {A} =  e₁ ⋆ e₂
  [_,_] .idᵣ = idᵣ   
  [_,_] .idₗ = idₗ   
  [_,_] .assₗ = assₗ

module _ (𝒞 : Category o₁ a₁ e₁) (𝒟 : Category o₂ a₂ e₂) where 
  open HomReasoning 𝒟 
  open Category 𝒟 ; open `Category 𝒞

  -- The "evaluation" functor, viewing [ 𝒟 , 𝒞 ] as an 
  -- exponential Dᶜ in the category 𝐂𝐚𝐭.                                         
  --        X × C                X
  --         |   \               |
  -- λg × id |    \ g            | λg
  --         v      v            v
  -- [C , D] × C --> D          [C , D]
  --             eval
  
  eval : ([ 𝒞 , 𝒟 ] × 𝒞) ⇛ 𝒟
  eval .Functor.F₀ (F , A) = F₀ A
    where open Functor F 
  eval .Functor.fmap 
    {A = F , A} {B = G , B} ((η , naturality) , f) = gmap f ∘ η
    where open Functor F ; open Gunctor G 
  eval .Functor.F-id {F , A} = F-id ⋆ₗ Id ⨾ idₗ
    where open Functor F  
  eval .Functor.F-∘ 
    {A = F , A} {B = G , B} {C = H , C} 
    ((η , nat-η) , f) ((ε , nat-ε) , g) = begin
      hmap (g `∘ f) ∘ (ε ∘ η)   ≈⟨ H-∘ f g ⋆ₗ (ε ∘ η) ⟩ 
      hmap g ∘ hmap f ∘ (ε ∘ η) ≈⟨ assₗ ⨾ assᵣ ⋆ₗ η ⟩ 
      hmap g ∘ (hmap f ∘ ε) ∘ η ≈⟨ hmap g ⋆ᵣ (nat-ε f) ⋆ₗ η ⟩ 
      hmap g ∘ (ε ∘ gmap f) ∘ η ≈⟨ assₗ ⋆ₗ η ⨾ assᵣ ⟩ 
      hmap g ∘ ε ∘ (gmap f ∘ η) ∎ 
    where open Functor F ; open Gunctor G ; open Hunctor H 
  eval .Functor.F-cong 
    {F , A} {G , B} 
    {(η , nat-η) , f} {(ε , nat-ε) , g} 
    (η≈ε , f≈g) = (G-cong f≈g) ⋆ η≈ε
    where open Gunctor G

module _ {𝒞 : Category o₁ a₁ e₁} {𝒟 : Category o₂ a₂ e₂} where 
  open HomReasoning 𝒟 
  open Category 𝒟 ; open `Category 𝒞

  -- Currying
  λ[_] : ∀ {𝒳 : Category o₃ a₃ e₃} → 
           (𝒳 × 𝒞) ⇛ 𝒟 → 
           𝒳 ⇛ [ 𝒞 , 𝒟 ]
  λ[ G ] .Functor.F₀ A = Bf-π₂ G A
  λ[ G ] .Functor.fmap f = TODO 
  λ[ G ] .Functor.F-id = TODO 
  λ[ G ] .Functor.F-∘ = TODO 
  λ[ G ] .Functor.F-cong = TODO

  -- If F is full then so is λ[ F ]
  λF-Full : ∀ {𝒳 : Category o₃ a₃ e₃} → 
           (F : (𝒳 × 𝒞) ⇛ 𝒟) → 
           Full F → 
           Full (λ[ F ])
  λF-Full = TODO 

  -- If F is faithful then so is λ[ F ]
  λF-Faithful : ∀ {𝒳 : Category o₃ a₃ e₃} → 
           (F : (𝒳 × 𝒞) ⇛ 𝒟) → 
           Faithful F → 
           Faithful (λ[ F ])
  λF-Faithful = TODO            
