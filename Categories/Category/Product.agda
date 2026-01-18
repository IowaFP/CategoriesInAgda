{-# OPTIONS --without-K #-}

module Categories.Category.Product where 

open import Categories.Prelude
open import Categories.Category.Base 
open import Categories.Functor.Base

--------------------------------------------------------------------------------
-- Product categories

module _ (𝒞 : Category o₁ a₁ e₁) (𝒟 : Category o₂ a₂ e₂) where
  open Category
  _×_ : Category (o₁ ⊔ o₂) (a₁ ⊔ a₂) (e₁ ⊔ e₂)
  _×_  .Obj = 𝒞 .Obj * 𝒟 .Obj
  _×_ ._⇒_ (A , B) (C , D) = (𝒞 [ A , C ])  * (𝒟 [ B , D ])
  _×_ ._∘_ (f₁ , f₂) (g₁ , g₂) = (𝒞 [ f₁ ∘ g₁ ]) , (𝒟 [ f₂ ∘ g₂ ])
  _×_ .Id = (𝒞 .Id) , (𝒟 .Id) 
  _×_ ._≈_ (f₁ , f₂) (g₁ , g₂) = 𝒞 [ f₁ ≈ g₁ ] * 𝒟 [ f₂ ≈  g₂ ]
  _×_ .eqv .IsEquivalence.refl {f , g} = refl-≈ 𝒞 , refl-≈ 𝒟
  _×_ .eqv .IsEquivalence.sym (f , g) = sym-≈ 𝒞 f , sym-≈ 𝒟 g
  _×_ .eqv .IsEquivalence.trans (f₁ , g₁) (f₂ , g₂) = trans-≈ 𝒞 f₁ f₂ , trans-≈ 𝒟 g₁ g₂
  _×_ .idᵣ = 𝒞 .idᵣ , 𝒟 .idᵣ
  _×_ .idₗ = 𝒞 .idₗ , 𝒟 .idₗ
  _×_ .assₗ = 𝒞 .assₗ , 𝒟 .assₗ
  _×_ .cong-∘ {f = f₁ , f₂} {h₁ , h₂} {g₁ , g₂} {i₁ , i₂} (f₁≈h₁ , f₂≈h₂) (g₁≈i₁ , g₂≈i₂)  = 
    (cong-∘ 𝒞 f₁≈h₁ g₁≈i₁) , (cong-∘ 𝒟 f₂≈h₂ g₂≈i₂) 



module _ {𝒞 : Category o₁ a₁ e₁} {𝒟 : Category o₂ a₂ e₂} where
  open Category
  open Functor 
  private
    module C = Category 𝒞
    module D = Category 𝒟

  -- Projecting the left category out of a product category
  π¹ : Functor (𝒞 × 𝒟) 𝒞
  π¹ .F₀ = fst
  π¹ .fmap = fst
  π¹ .F-id = C.refl-≈
  π¹ .F-∘ _ _ = C.refl-≈
  π¹ .F-cong = fst 

  -- Projecting the right category
  π² : Functor (𝒞 × 𝒟) 𝒟 
  π² .F₀ = snd
  π² .fmap = snd
  π² .F-id = D.refl-≈
  π² .F-∘ _ _ = D.refl-≈
  π² .F-cong = snd 

module _ {𝒞 : Category o₁ a₁ e₁} {𝒟 : Category o₂ a₂ e₂} {ℰ : Category o₃ a₃ e₃} where
  open Category
  private
    module C = Category 𝒞
    module D = Category 𝒟

  -- The product of two functors---or, when viewing products of categories
  -- as binary products in the category of categories, we can view 
  -- ⟨ F ⨾ G ⟩ as giving the unique morphism H : 𝒞 → D × ℰ that commutes
  -- with π¹ and π². (See Categories.Instances.Cats)
  ⟨_,_⟩ : ∀ (F : Functor 𝒞 𝒟) → (G : Functor 𝒞 ℰ) → Functor 𝒞 (𝒟 × ℰ)
  ⟨ F , G ⟩ = record
    { F₀         = < F₀ , G₀ >
    ; fmap       = < fmap , gmap > 
    ; F-id       = F-id , G-id
    ; F-∘        = λ f g → F-∘ f g , G-∘ f g
    ; F-cong     = < F-cong , G-cong > 
    }
    where 
      open Functor F ; open Gunctor G