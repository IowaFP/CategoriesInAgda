{-# OPTIONS --without-K #-}

module Categories.Functor.Base where 

open import Categories.Prelude
open import Categories.Category.Base
open import Categories.Category.Arrows
open import Categories.Reasoning.Hom

--------------------------------------------------------------------------------
-- Functors

module _ (𝒞 : Category o₁ a₁ e₁) (𝒟 : Category o₂ a₂ e₂) where 
  open Category 𝒞 
  open `Category 𝒟
  
  private 
    variable 
      A B C D : Obj
      f g h : A ⇒ B

  record Functor : Set (o₁ ⊔ o₂ ⊔ a₁ ⊔ a₂ ⊔ e₁ ⊔ e₂) where
    field 
      -- Set (o₁ ⊔ o₂)
      F₀ : Obj → `Obj 
      -- Set (o₁ ⊔ a₁ ⊔ a₂)
      fmap : A ⇒ B → F₀ A `⇒ F₀ B 
      -- o₁ ⊔ e₂
      F-id : fmap {A} Id `≈ `Id 
      -- o₁ ⊔ a₁ ⊔ e₂ 
      F-∘ : (f : A ⇒ B) (g : B ⇒ C) → fmap (g ∘ f) `≈ fmap g `∘ fmap f
      -- Set (o₁ ⊔ a₁ ⊔ e₁ ⊔ e₂)
      F-cong : f ≈ g → fmap f `≈ fmap g

    infixl 5 _$_ 
    _$_ = fmap
    ₀ = F₀ 
    ₁ = fmap

Endofunctor : Category o a e → Set (o ⊔ a ⊔ e) 
Endofunctor 𝒞 = Functor 𝒞 𝒞 

--------------------------------------------------------------------------------
-- Common syntax 

module Gunctor {𝒞 : Category o₁ a₁ e₁} {𝒟 : Category o₂ a₂ e₂} (G : Functor 𝒞 𝒟) where 
  open Functor G 
    renaming (F₀ to G₀ ; 
            fmap to gmap ; 
            F-id to G-id ; 
             F-∘ to G-∘ ; 
          F-cong to G-cong) public

module Hunctor {𝒞 : Category o₁ a₁ e₁} {𝒟 : Category o₂ a₂ e₂} (H : Functor 𝒞 𝒟) where 
  open Functor H 
    renaming (F₀ to H₀ ; 
            fmap to hmap ; 
            F-id to H-id ; 
             F-∘ to H-∘ ; 
          F-cong to H-cong) public

--------------------------------------------------------------------------------
-- Functor composition

module _ {𝒞 : Category o₁ a₁ e₁} {𝒟 : Category o₂ a₂ e₂} {ℰ : Category o₃ a₃ e₃} (F : Functor 𝒟 ℰ) (G : Functor 𝒞 𝒟) where 
  open Category ℰ 
  open HomReasoning ℰ 

  open Functor F 
  open Functor G renaming (F₀ to G₀ ; fmap to gmap ; F-id to G-id ; F-∘ to G-∘ ; F-cong to G-cong)

  _∘F_ : Functor 𝒞 ℰ 
  _∘F_ .Functor.F₀ = (F₀ ○ G₀)
  _∘F_ .Functor.fmap = fmap ○ gmap 
  _∘F_ .Functor.F-id {A} = 
    begin 
      (fmap (gmap (Category.Id 𝒞)) ≈⟨ F-cong G-id ⟩ 
      fmap (Category.Id 𝒟) ≈⟨ F-id ⟩ 
      Id ∎)
  _∘F_ .Functor.F-∘ f g = 
    begin 
      fmap (gmap (𝒞 [ g ∘ f ])) ≈⟨ F-cong (G-∘ f g) ⟩ 
      fmap (𝒟 [ gmap g ∘ gmap f ]) ≈⟨ F-∘ (gmap f) (gmap g) ⟩ 
      fmap (gmap g) ∘ (fmap (gmap f)) ∎ 
  _∘F_ .Functor.F-cong = F-cong ○ G-cong 

--------------------------------------------------------------------------------
-- The identity functor

module _ {𝒞 : Category o a e} where 
  open Category 𝒞 
  open Functor 

  -- The identity functor 
  IdF : Functor 𝒞 𝒞 
  IdF .F₀ = id 
  IdF .fmap = id 
  IdF .F-id = refl-≈
  IdF .F-∘ _ _ = refl-≈ 
  IdF .F-cong = id 


--------------------------------------------------------------------------------
-- The constant functor

module _ {𝒞 : Category o₁ a₁ e₁} {𝒟 : Category o₂ a₂ e₂} (A : 𝒟 .Category.Obj) where 
  open Category 𝒟
  open Functor 

  Const : Functor 𝒞 𝒟 
  Const .F₀ _ = A
  Const .fmap f = Id
  Const .F-id = refl-≈
  Const .F-∘ f g = sym-≈ idₗ
  Const .F-cong eq = refl-≈ 

--------------------------------------------------------------------------------
-- Opposite functors

module _ {𝒞 : Category o₁ a₁ e₁} {𝒟 : Category o₂ a₂ e₂} (F : Functor 𝒞 𝒟) where 
  open Category 
  open Functor F 
  private 
    module C = Category 𝒞 ; module D = Category 𝒟 

  -- A functor from 𝒞 to 𝒟 is also a contravariant functor into 𝒟ᵒᵖ. 
  opF : Functor (op 𝒞) (op 𝒟)
  opF .Functor.F₀ = F₀
  opF .Functor.fmap = fmap
  opF .Functor.F-id = F-id
  opF .Functor.F-∘ = λ f g → F-∘ g f
  opF .Functor.F-cong = F-cong 

--------------------------------------------------------------------------------
-- Isomorphisms are preserved by functors

module _ {𝒞 : Category o₁ a₁ e₁} {𝒟 : Category o₂ a₂ e₂} (F : Functor 𝒞 𝒟) where 
  open Category 𝒟 ; open HomReasoning 𝒟 
  open Functor F 

  private 
    module C = Category 𝒞 ; module Cᵢ = Isomorphism 𝒞 ; module Dᵢ = Isomorphism 𝒟 
  
  iso-preservation : ∀ {A B : C.Obj} (f : A C.⇒ B) (g : B C.⇒ A) → 
                        areInverse 𝒞 f g → areInverse 𝒟 (fmap f) (fmap g)
  iso-preservation f g (linv , rinv) = 
    (begin 
      (fmap f ∘ fmap g) ≈⟨ sym-≈ (F-∘ g f) ⟩ 
      (fmap (f C.∘ g))  ≈⟨ F-cong linv ⟩ 
      (fmap C.Id)       ≈⟨ F-id ⟩ 
      Id ∎) , 
    (begin 
      (fmap g ∘ fmap f) ≈⟨ sym-≈ (F-∘ f g) ⟩ 
      (fmap (g C.∘ f))  ≈⟨ F-cong rinv ⟩ 
      (fmap C.Id)       ≈⟨ F-id ⟩ 
      Id ∎) 

  --------------------------------------------------------------------------------
  -- Full and faithful functors
  
  -- F is injective on hom-sets
  Faithful : Set _
  Faithful = ∀ {A B : C.Obj} → (f : A C.⇒ B) (g : A C.⇒ B) → 
               fmap f ≈ fmap g → 
               f C.≈ g 

-- F is surjective on hom-sets
  Full : Set _
  Full = ∀ {A B : C.Obj} → (g : F₀ A ⇒ F₀ B) → 
               Σ[ f ∈ (A C.⇒ B) ] (fmap f ≈ g)
  
  FullyFaithful = Faithful * Full

  --------------------------------------------------------------------------------
  -- Essential injectivity/surjectivity

  -- F is injective on objects (up to isomorphism)
  EssentiallyInjective : Set _
  EssentiallyInjective = ∀ {A B : C.Obj} → F₀ A Dᵢ.≃ F₀ B → A Cᵢ.≃ B

  -- F is surjective on objects (up to isomorphism)
  EssentiallySurjective : Set _
  EssentiallySurjective = (d : Obj) → Σ[ c ∈ C.Obj ] (F₀ c Dᵢ.≃ d)

  -- Full and faithful functors are injective on objects up to isomorphism
  injectiveOnObjects : FullyFaithful → EssentiallyInjective 
  injectiveOnObjects ff iso = {!   !} 







