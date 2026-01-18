{-# OPTIONS --without-K #-}

module Categories.Instances.Cats where 

open import Categories.Prelude
open import Categories.Category
open import Categories.Functor 
open import Categories.NaturalTransformation

--------------------------------------------------------------------------------
-- The Category of Categories 

open Category 
Cats : ∀ (o a e : Level) → Category (lsuc (o ⊔ a ⊔ e)) (lsuc o ⊔ a ⊔ e) (o ⊔ a ⊔ e) 
Cats o a e .Obj = Category o a e
Cats o a e ._⇒_ 𝒞 𝒟 =  Functor 𝒞 𝒟
Cats o a e ._∘_ = _∘F_
Cats o a e .Id = IdF 
Cats o a e ._≈_ {𝒞} {𝒟} F G =  F ≃ₙ G
Cats o a e .eqv  = nat-setoid .Setoid.isEquivalence
Cats o a e .cong-∘ {A = A} {B} {C} {f = F} {H} {G} {I} η₁ η₂ = H-iso η₂ η₁
Cats o a e .right-id =  IdF-right-id  
Cats o a e .left-id = IdF-left-id   
Cats o a e .assₗ {f = F} {G} {H} = Functor-assₗ F G H 