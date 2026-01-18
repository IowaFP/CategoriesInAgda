{-# OPTIONS --without-K #-}
module Categories.Instances.Groupoids where

open import Categories.Prelude
open import Categories.Category
open import Categories.Functor 
open import Categories.NaturalTransformation
open import Categories.Constructions.Groupoid
open import Categories.Constructions.Preorder

open PropositionalEquality hiding (isPreorder)

--------------------------------------------------------------------------------
-- The category of groupoids

module _  where
  open Category 
  open GroupoidCategory
  
  Groupoids : ∀ (o a e : Level) → Category (lsuc (o ⊔ a ⊔ e)) (lsuc o ⊔ a ⊔ e) (o ⊔ a ⊔ e) 
  Groupoids o a e  .Obj = GroupoidCategory o a e
  Groupoids o a e ._⇒_ 𝒞 𝒟 =  Functor (𝒞 .category) (𝒟 .category)
  Groupoids o a e ._∘_ = _∘F_
  Groupoids o a e .Id = IdF 
  Groupoids o a e ._≈_ {𝒞} {𝒟} F G = F ≃ₙ G
  Groupoids o a e .eqv  = nat-setoid .Setoid.isEquivalence
  Groupoids o a e .cong-∘ {A = A} {B} {C} {f = F} {H} {G} {I} η₁ η₂ = H-iso η₂ η₁
  Groupoids o a e .idᵣ =  IdF-idᵣ  
  Groupoids o a e .idₗ = IdF-idₗ   
  Groupoids o a e .assₗ {f = F} {G} {H} = Functor-assₗ F G H 