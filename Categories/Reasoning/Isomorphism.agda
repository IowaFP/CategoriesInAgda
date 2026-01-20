{-# OPTIONS --without-K #-}

module Categories.Reasoning.Isomorphism where 

open import Categories.Prelude
open import Categories.Category.Base
open import Categories.Category.Arrows

open import Relation.Binary.Reasoning.Syntax using (module ≃-syntax ; module ≈-syntax)

--------------------------------------------------------------------------------
-- Object isomorphism reasoning syntax

module IsoReasoning  
    (𝒞 : Category o₁ a₁ e₁) where 
  open Isomorphism 𝒞 
  open Setoid Objs

  open import Relation.Binary.Reasoning.Base.Single (_≃_) refl trans 
    renaming (∼-go to ≃-go) public

  open ≃-syntax _IsRelatedTo_ _IsRelatedTo_ ≃-go sym public 