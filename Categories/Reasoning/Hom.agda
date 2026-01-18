{-# OPTIONS --without-K #-}
module Categories.Reasoning.Hom where 

open import Categories.Prelude
open import Categories.Category.Base

--------------------------------------------------------------------------------
-- Reasoning syntax 

module HomReasoning (𝒞 : Category a e o) {A B : 𝒞 .Category.Obj} where
  open Category 𝒞 
  open import Relation.Binary.Reasoning.Setoid (hom-setoid A B) public