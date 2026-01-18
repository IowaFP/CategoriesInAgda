{-# OPTIONS --without-K #-}

module Categories.Functor.Bifunctor where 

open import Categories.Prelude
open import Categories.Category.Base 
open import Categories.Functor.Base
open import Categories.Category.Product

--------------------------------------------------------------------------------
-- Bifunctors


Bifunctor : Category o₁ a₁ e₁ → Category o₂ a₂ e₂ → Category o₃ a₃ e₃ → 
            Set (lsuc o₁ ⊔ a₁ ⊔ e₁ ⊔ lsuc o₂ ⊔ a₂ ⊔ e₂ ⊔ lsuc o₃ ⊔ a₃ ⊔ e₃)
Bifunctor 𝒞 𝒟 ℰ = Functor (𝒞 × 𝒟) ℰ

module _ {𝒞 : Category o₁ a₁ e₁} 
         {𝒟 : Category o₂ a₂ e₂} 
         {ℰ : Category o₃ a₃ e₃} 
         (F : Bifunctor 𝒞 𝒟 ℰ) where 
  open Category {{...}}
  instance 
    _ : Category o₂ a₂ e₂ 
    _ = 𝒟

  open Functor F   

  -- Projecting a unary functor from a bifunctor
  BFPrj₁ : (A : 𝒟 .Obj) → Functor 𝒞 ℰ
  BFPrj₁ A .F₀ = F₀ ○ (_, A) 
  BFPrj₁ A .fmap  f = fmap (f , Id) 
  BFPrj₁ A .F-id  = F-id 
  BFPrj₁ A .F-∘ f g = trans-≈ ⦃ ℰ ⦄ 
    (F-cong ((refl-≈ {{𝒞}}) , sym-≈ {{𝒟}} (right-id {{𝒟}}))) 
    (F-∘ (f , Id) (g , Id)) 
  BFPrj₁ A .F-cong f≈g = F-cong (f≈g , (refl-≈ {{𝒟}}))

  BFPrj₂ : (A : 𝒞 .Obj) → Functor 𝒟 ℰ
  BFPrj₂ A .F₀ = F₀ ○ (A ,_) 
  BFPrj₂ A .fmap  f = fmap (Id {{𝒞}} , f)
  BFPrj₂ A .F-id  = F-id 
  BFPrj₂ A .F-∘ f g = trans-≈ ⦃ ℰ ⦄ 
    (F-cong ((sym-≈ {{𝒞}} (right-id {{𝒞}})) , (refl-≈ {{𝒟}}))) 
    (F-∘ (Id {{𝒞}} , f) (Id {{𝒞}} , g))
  BFPrj₂ A .F-cong f≈g = F-cong ((refl-≈ {{𝒞}}) , f≈g)    