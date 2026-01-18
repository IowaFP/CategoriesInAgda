module Categories.Category.Equivalence where

open import Categories.Prelude
open import Categories.Category
open import Categories.Functor 
open import Categories.NaturalTransformation

--------------------------------------------------------------------------------
-- Definition 1: 𝒞 and 𝒟 are equivalent if there is a pair of functors
--   F : 𝒞 ←→ 𝒟 : G 
-- such that 
--   F ○ G ≃ₙ IdF   and   G ○ F ≃ₙ IdF

module Definition1 (𝒞 𝒟 : Category o a e) where
  open import Categories.Instances.Cats
  open Isomorphism (Cats o a e)

  -- In other words, 𝒞 and 𝒟 are isomorphic objects in the category of categories
  areEquivalent : Set _
  areEquivalent = 𝒞 ≃ 𝒟 
  
  -- TODO: Adjoint equivalence

--------------------------------------------------------------------------------
-- Definition 2: 𝒞 and 𝒟 are equivalent if there exists an essentially
-- surjective and fully faithful functor F : 𝒞 → 𝒟.

module Definition2 (𝒞 𝒟 : Category o a e) where

  record areEquivalent : Set (lsuc (o ⊔ a ⊔ e)) where 
    field 
        F : Functor 𝒞 𝒟
        essentiallySurjective : EssentiallySurjective F 
        fullyFaithful : FullyFaithful F

--------------------------------------------------------------------------------
-- todo: these definitions are equivalent.

module _ (𝒞 𝒟 : Category o a e) where
    
  Def1⇒Def2 : Definition1.areEquivalent 𝒞 𝒟 → Definition2.areEquivalent 𝒞 𝒟
  Def1⇒Def2 eqv = {!   !} 

  Def2⇒Def1 : Definition2.areEquivalent 𝒞 𝒟 → Definition1.areEquivalent 𝒞 𝒟
  Def2⇒Def1 eqv = {!   !} 