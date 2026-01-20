{-# OPTIONS --without-K #-}

module Categories.Reasoning.NaturalIsomorphism where 

open import Categories.Prelude
open import Categories.Category
open import Categories.NaturalTransformation

open import Relation.Binary.Reasoning.Syntax using (module ≃-syntax)

--------------------------------------------------------------------------------
-- Natural isomorphism reasoning syntax

module NatIsoReasoning  
    (𝒞 : Category o₁ a₁ e₁) 
    (𝒟 : Category o₂ a₂ e₂) where 

  open Setoid (Fun(𝒞 , 𝒟))
  open import Relation.Binary.Reasoning.Base.Single (_≃ₙ_) refl trans 
    renaming (∼-go to ≃ₙ-go) public
  open ≃-syntax _IsRelatedTo_ _IsRelatedTo_ ≃ₙ-go sym public 
