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
      F₀ : Obj → `Obj 
      fmap : A ⇒ B → F₀ A `⇒ F₀ B 
      F-id : fmap {A} Id `≈ `Id 
      F-∘ : (f : A ⇒ B) (g : B ⇒ C) → fmap (g ∘ f) `≈ fmap g `∘ fmap f
      F-cong : f ≈ g → fmap f `≈ fmap g

    infixl 5 _$_ 
    _$_ = fmap
    ₀ = F₀ 
    ₁ = fmap

-- Infix notation for Functor
infixr 5 _⇛_ 
_⇛_ = Functor 

-- An endofunctor is a functor with equal domain & codomain
Endofunctor : Category o a e → Set (o ⊔ a ⊔ e) 
Endofunctor 𝒞 = Functor 𝒞 𝒞 

--------------------------------------------------------------------------------
-- Common syntax 

module Gunctor {𝒞 : Category o₁ a₁ e₁} {𝒟 : Category o₂ a₂ e₂} (G : 𝒞 ⇛ 𝒟) where 
  open Functor G 
    renaming (F₀ to G₀ ; 
            fmap to gmap ; 
            F-id to G-id ; 
             F-∘ to G-∘ ; 
          F-cong to G-cong) public

module Hunctor {𝒞 : Category o₁ a₁ e₁} {𝒟 : Category o₂ a₂ e₂} (H : 𝒞 ⇛ 𝒟) where 
  open Functor H 
    renaming (F₀ to H₀ ; 
            fmap to hmap ; 
            F-id to H-id ; 
             F-∘ to H-∘ ; 
          F-cong to H-cong) public

module Junctor {𝒞 : Category o₁ a₁ e₁} {𝒟 : Category o₂ a₂ e₂} (J : 𝒞 ⇛ 𝒟) where 
  open Functor J 
    renaming (F₀ to J₀ ; 
            fmap to jmap ; 
            F-id to J-id ; 
             F-∘ to J-∘ ; 
          F-cong to J-cong) public

module Kunctor {𝒞 : Category o₁ a₁ e₁} {𝒟 : Category o₂ a₂ e₂} (K : 𝒞 ⇛ 𝒟) where 
  open Functor K 
    renaming (F₀ to K₀ ; 
            fmap to kmap ; 
            F-id to K-id ; 
             F-∘ to K-∘ ; 
          F-cong to K-cong) public

--------------------------------------------------------------------------------
-- Functor composition

module _ {𝒞 : Category o₁ a₁ e₁} {𝒟 : Category o₂ a₂ e₂} {ℰ : Category o₃ a₃ e₃} 
  (F : 𝒟 ⇛ ℰ) (G : 𝒞 ⇛ 𝒟) where 
  open Category ℰ 
  open HomReasoning ℰ 

  open Functor F ; open Gunctor G 

  _∘F_ : 𝒞 ⇛ ℰ 
  _∘F_ .Functor.F₀ = (F₀ ○ G₀)
  _∘F_ .Functor.fmap = fmap ○ gmap 
  _∘F_ .Functor.F-id {A} = 
    begin 
      (fmap (gmap (Category.Id 𝒞)) ≈⟨ F-cong G-id ⟩ 
      fmap (Category.Id 𝒟)         ≈⟨ F-id ⟩ 
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

  Const : 𝒞 ⇛ 𝒟 
  Const .F₀ _ = A
  Const .fmap f = Id
  Const .F-id = refl-≈
  Const .F-∘ f g = sym-≈ idₗ
  Const .F-cong eq = refl-≈ 

--------------------------------------------------------------------------------
-- Opposite functors

module _ {𝒞 : Category o₁ a₁ e₁} {𝒟 : Category o₂ a₂ e₂} (F : 𝒞 ⇛ 𝒟) where 
  open Category 
  open Functor F 
  private 
    module C = Category 𝒞 ; module D = Category 𝒟 

  -- A functor from 𝒞 to 𝒟 is also a contravariant functor into 𝒟ᵒᵖ. 
  opF : (op 𝒞) ⇛ (op 𝒟)
  opF .Functor.F₀ = F₀
  opF .Functor.fmap = fmap
  opF .Functor.F-id = F-id
  opF .Functor.F-∘ = λ f g → F-∘ g f
  opF .Functor.F-cong = F-cong 

--------------------------------------------------------------------------------
-- Isomorphisms are preserved by functors

module _ {𝒞 : Category o₁ a₁ e₁} {𝒟 : Category o₂ a₂ e₂} (F : 𝒞 ⇛ 𝒟) where 
  open `Category 𝒞 ; open Category 𝒟 ; open HomReasoning 𝒟 
  open Functor F ; open `Isomorphism 𝒞 ; open Isomorphism 𝒟 

  private variable A B C : `Obj 
  
  iso-preservation : (f : A `⇒ B) (g : B `⇒ A) → 
                      areInverse 𝒞 f g → 
                      areInverse 𝒟 (fmap f) (fmap g)
  iso-preservation f g (linv , rinv) = 
    (begin 
      (fmap f ∘ fmap g) ≈⟨ (F-∘ g f) ⁻¹ ⟩ 
      (fmap (f `∘ g))  ≈⟨ F-cong linv ⟩ 
      (fmap `Id)       ≈⟨ F-id ⟩ 
      Id ∎) , 
    (begin 
      (fmap g ∘ fmap f) ≈⟨ (F-∘ f g) ⁻¹ ⟩ 
      (fmap (g `∘ f))  ≈⟨ F-cong rinv ⟩ 
      (fmap `Id)       ≈⟨ F-id ⟩ 
      Id ∎) 

  --------------------------------------------------------------------------------
  -- Full and faithful functors
  
  -- F is injective on hom-sets
  Faithful : Set _
  Faithful = ∀ {A B : `Obj} (f : A `⇒ B) (g : A `⇒ B) → 
               fmap f ≈ fmap g → 
               f `≈ g 

-- F is surjective on hom-sets
  Full : Set _
  Full = ∀ {A B : `Obj} (g : F₀ A ⇒ F₀ B) → 
          Σ[ f ∈ (A `⇒ B) ] (fmap f ≈ g)
  
  FullyFaithful = Faithful * Full

  --------------------------------------------------------------------------------
  -- Essential injectivity/surjectivity

  -- F is injective on objects (up to isomorphism)
  EssentiallyInjective : Set _
  EssentiallyInjective = ∀ {A B : `Obj} → 
                         F₀ A ≃ F₀ B → A `≃ B

  -- F is surjective on objects (up to isomorphism)
  EssentiallySurjective : Set _
  EssentiallySurjective = (B : Obj) → Σ[ A ∈ `Obj ] (F₀ A ≃ B)

  -- Full and faithful functors are injective on objects up to isomorphism
  injectiveOnObjects : FullyFaithful → EssentiallyInjective 
  injectiveOnObjects ff iso = {!   !} 







