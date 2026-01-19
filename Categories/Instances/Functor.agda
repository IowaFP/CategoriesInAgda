{-# OPTIONS --without-K #-}

module Categories.Instances.Functor where 

open import Categories.Prelude
open import Categories.Category 
open import Categories.Functor 
open import Categories.NaturalTransformation 
open import Categories.Category.Product
open import Categories.Instances.Setoid
open import Categories.Reasoning.Hom 

--------------------------------------------------------------------------------
-- The Category of functors [𝒞 , 𝒟]

module _ (𝒞 : Category o₁ a₁ e₁) (𝒟 : Category o₂ a₂ e₂) where 
  open Category 𝒟 
  open HomReasoning 𝒟
  open _≃ₙ_

  [_,_] : Category _ _ _
  [_,_] .Obj = Functor 𝒞 𝒟 
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