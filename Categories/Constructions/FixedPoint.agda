{-# OPTIONS --without-K #-}

module Categories.Constructions.FixedPoint where 

open import Categories.Prelude
open import Categories.Category 
open import Categories.Functor 
open import Categories.NaturalTransformation

open import Categories.Constructions.Initial
open import Categories.Constructions.FAlgebra
open import Categories.Reasoning.Hom 

--------------------------------------------------------------------------------
-- Fixed-points of endofunctors on category 𝒞 

module _ (𝒞 : Category o a e) where 
  open Category 𝒞 
  open Functor 
  open Isomorphism 𝒞 

  FixedPoint : (F : Endofunctor 𝒞) → Set _ 
  FixedPoint F A = F .F₀ A ≃ A 


-- ------------------------------------------------------------------------------
-- Fixed-points form a category

module _ (𝒞 : Category o a e)
         (F : Endofunctor 𝒞) where 
  open Category 𝒞
  open Functor F 
  open IsEquivalence
  module C = Category 𝒞

  FAlgebras : Category (o ⊔ a) (a ⊔ e) e 
  FAlgebras .Category.Obj = FAlg 𝒞 F 
  FAlgebras .Category._⇒_ =  Hom
  FAlgebras .Category._∘_ = _∘FA_
  FAlgebras .Category.Id = IdHom
  FAlgebras .Category._≈_ (f , _) (g , _) =  f ≈ g
  FAlgebras .Category.eqv  .refl = refl-≈
  FAlgebras .Category.eqv  .sym = sym-≈
  FAlgebras .Category.eqv  .trans = trans-≈
  FAlgebras .Category.cong-∘  = cong-∘
  FAlgebras .Category.idᵣ =  idᵣ
  FAlgebras .Category.idₗ = idₗ