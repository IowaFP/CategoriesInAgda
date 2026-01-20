{-# OPTIONS --without-K #-}
module Categories.Instances.Groupoid where

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
  
  𝐆𝐩𝐝 : ∀ (o a e : Level) → Category (lsuc (o ⊔ a ⊔ e)) (o ⊔ a ⊔ e) (o ⊔ a ⊔ e) 
  𝐆𝐩𝐝 o a e  .Obj = GroupoidCategory o a e
  𝐆𝐩𝐝 o a e ._⇒_ 𝒞 𝒟 =  Functor (𝒞 .category) (𝒟 .category)
  𝐆𝐩𝐝 o a e ._∘_ = _∘F_
  𝐆𝐩𝐝 o a e .Id = IdF 
  𝐆𝐩𝐝 o a e ._≈_ {𝒞} {𝒟} F G = F ≃ₙ G
  𝐆𝐩𝐝 o a e .eqv  = functor-setoid .Setoid.isEquivalence
  𝐆𝐩𝐝 o a e ._⋆_ {A = A} {B} {C} {f = F} {H} {G} {I} η₁ η₂ = H-iso η₂ η₁
  𝐆𝐩𝐝 o a e .idᵣ =  IdF-idᵣ  
  𝐆𝐩𝐝 o a e .idₗ = IdF-idₗ   
  𝐆𝐩𝐝 o a e .assₗ {f = F} {G} {H} = Functor-assₗ F G H 