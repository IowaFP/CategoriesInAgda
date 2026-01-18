{-# OPTIONS --without-K #-}

module Categories.Instances.Functors where 

open import Categories.Prelude
open import Categories.Category 
open import Categories.Functor 
open import Categories.NaturalTransformation 
open import Categories.Category.Product
open import Categories.Instances.Setoids
open import Categories.Reasoning.Hom 

--------------------------------------------------------------------------------
-- The Category of functors [𝒞 , 𝒟]

module _ (𝒞 : Category o₁ a₁ e₁) (𝒟 : Category o₂ a₂ e₂) where 
  open Category 𝒟 
  open HomReasoning 𝒟
  open _≃ₙ_

  Functors : Category (lsuc o₁ ⊔ a₁ ⊔ e₁ ⊔ lsuc o₂ ⊔ a₂ ⊔ e₂) (o₁ ⊔ a₁ ⊔ e₁ ⊔ o₂ ⊔ a₂ ⊔ e₂) (o₁ ⊔ e₂)
  Functors .Obj = Functor 𝒞 𝒟
  Functors ._⇒_ = NaturalTransformation
  Functors ._∘_ {A = F} {G} {H} = _∘V_
  Functors .Id = IdN .nat 
  _≈_ Functors {A} {B} (η , nat-η) (ε , nat-ε) = ∀ {A : 𝒞 .Category.Obj} → η {A} ≈ ε {A}
  Functors .eqv .IsEquivalence.refl = refl-≈ 
  Functors .eqv .IsEquivalence.sym x≈y {A} = sym-≈ (x≈y {A})
  Functors .eqv .IsEquivalence.trans x≈y y≈z {A} = trans-≈ (x≈y {A}) (y≈z {A})
  Functors .cong-∘ {f = f} {h} {g} {i} e₁ e₂ {A} =  cong-∘ (e₁ {A}) (e₂ {A}) 
  Functors .right-id = right-id   
  Functors .left-id = left-id   
  Functors .assₗ = assₗ   