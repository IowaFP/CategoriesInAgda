{-# OPTIONS --without-K #-}

module Categories.Functor.Bifunctor where 

open import Categories.Prelude
open import Categories.Category.Base 
open import Categories.Functor.Base
open import Categories.Category.Product

--------------------------------------------------------------------------------
-- Bifunctors


Bifunctor : Category o₁ a₁ e₁ → Category o₂ a₂ e₂ → Category o₃ a₃ e₃ → 
            Set (o₁ ⊔ a₁ ⊔ e₁ ⊔ o₂ ⊔ a₂ ⊔ e₂ ⊔ o₃ ⊔ a₃ ⊔ e₃)
Bifunctor 𝒞 𝒟 ℰ = (𝒞 × 𝒟) ⇛ ℰ

module _ {𝒞 : Category o₁ a₁ e₁} 
         {𝒟 : Category o₂ a₂ e₂} 
         {ℰ : Category o₃ a₃ e₃} 
         (F : Bifunctor 𝒞 𝒟 ℰ) where 
  open Category 
  open Functor F   

  -- Projecting a unary functor from a bifunctor
  Bf-π₁ : (A : 𝒟 .Obj) → 𝒞 ⇛ ℰ
  Bf-π₁ A = F ∘F ⟨ IdF , Const A ⟩

  Bf-π₂ : (A : 𝒞 .Obj) → 𝒟 ⇛ ℰ
  Bf-π₂ A = F ∘F ⟨ Const A , IdF ⟩ 