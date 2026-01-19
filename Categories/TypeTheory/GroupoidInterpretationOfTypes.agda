{-# OPTIONS --without-K #-}
module Categories.TypeTheory.GroupoidInterpretationOfTypes where

open import Categories.Prelude
open import Categories.Category
open import Categories.Functor 
open import Categories.NaturalTransformation

open import Categories.Constructions.Groupoid
open import Categories.Constructions.Preorder
open import Categories.Constructions.Discrete
open import Categories.Constructions.Initial
open import Categories.Constructions.Terminal

open import Categories.Instances.Groupoid
open import Categories.Instances.Cat

open PropositionalEquality hiding (isPreorder ; preorder ; _⨾_)

--------------------------------------------------------------------------------
-- - The groupoid interpretation of type theory. 
--   Martin Hofmann and Thomas Streicher. 1996
--   - https://ncatlab.org/nlab/files/HofmannStreicherGroupoidInterpretation.pdf

module _ (A : Set o) where
  open Category 
  open Equivalence
  
  -- A category with types as objects and identifications as arrows.
  Types : GroupoidCategory o o o 
  Types .category .Obj = A
  Types .category ._⇒_ a b = a ≡ b
  Types .category ._∘_ = flip trans
  Types .category .Id = refl
  Types .category ._≈_  = _≡_ 
  Types .category .eqv .IsEquivalence.refl = refl
  Types .category .eqv .IsEquivalence.sym  = sym
  Types .category .eqv .IsEquivalence.trans  = trans
  Types .category ._⋆_  refl refl = refl
  Types .category .idᵣ  = refl 
  Types .category .idₗ {f = refl} = refl 
  Types .category .assₗ {f = refl} {refl} {refl} = refl
  Types .groupoid = Groupoid (λ { refl → refl , refl , refl }) 

--------------------------------------------------------------------------------
-- The UIP is equivalent to the statement that Types is discrete (recall 
-- that a discrete category is a preorder groupoid.)
-- The translation is immediate.

  UIP : Set o  
  UIP = ∀ {a b : A} → (p q : a ≡ b) → p ≡ q 

  UIP⇔Preorder : UIP ⇔ isPreorder (Types .category)
  UIP⇔Preorder .to = Preorder
  UIP⇔Preorder .from = preorder
  UIP⇔Preorder .to-cong = cong Preorder
  UIP⇔Preorder .from-cong = cong preorder

--------------------------------------------------------------------------------
  -- Δ[ X ] forms the *discrete groupoid category* over X, 
  -- with only identities as morphisms. We generalize from the setoid (X , _≡_)
  -- to arbitrary setoid.
  
module _ (A : Setoid ℓ₁ ℓ₂) where 
  open Category 
  open Equivalence
  open Setoid A 
    using (Carrier) 
    renaming (_≈_ to _∼_ ; refl to refl-∼ ; sym to sym-∼ ; trans to trans-∼)

  Δ[_] : GroupoidCategory ℓ₁ ℓ₂ e 
  Δ[_] .category .Obj = Carrier
  Δ[_] .category ._⇒_ = _∼_
  Δ[_] .category ._∘_ = flip trans-∼ 
  Δ[_] .category .Id = refl-∼
  Δ[_] .category ._≈_  _ _ = ⊤ 
  Δ[_] .category .eqv .IsEquivalence.refl = tt
  Δ[_] .category .eqv .IsEquivalence.sym  = λ _ → tt 
  Δ[_] .category .eqv .IsEquivalence.trans  = λ _ _ → tt
  Δ[_] .category ._⋆_  = λ _ _ → tt
  Δ[_] .category .idᵣ  = tt 
  Δ[_] .category .idₗ  = tt
  Δ[_] .category .assₗ  = tt
  Δ[_] .groupoid = Groupoid λ { A∼B → sym-∼ A∼B , tt , tt }

  Δ[]IsPreorder : ∀ {e} → isPreorder {e = e}  (Δ[_] .category)
  Δ[]IsPreorder = Preorder  (λ _ _ → tt)

  Δ[]IsDiscrete : isDiscrete {e = e} (Δ[_] .category)
  Δ[]IsDiscrete = Discrete (Δ[_] .groupoid)  Δ[]IsPreorder

--------------------------------------------------------------------------------
-- Δ[ ⊤ ] is terminal in the category of groupoids.

⊤-terminal : isTerminal (𝐆𝐩𝐝 o o o) (Δ[ ≡-setoid {A = ⊤} ])
⊤-terminal {o = o} = term F λ {𝒞} → unique {𝒞}
  where 
    open Functor 
    F : ∀ (𝒞 : GroupoidCategory o o o) → 
           Functor {o₂ = o} {e₂ = o} (𝒞 .category) (Δ[ ≡-setoid {A = ⊤} ] .category)
    F 𝒞 .F₀ _ =  tt 
    F 𝒞 .fmap _ = refl 
    F 𝒞 .F-id = tt 
    F 𝒞 .F-∘ _ _ = tt 
    F 𝒞 .F-cong _ = tt 

    unique : ∀ {𝒞 : GroupoidCategory o o o} → 
                (G : Functor (𝒞 .category) (Δ[ ≡-setoid {A = ⊤} ] .category)) → 
                G ≃ₙ (F 𝒞)
    unique G = (refl , λ _ → tt) , refl , tt , tt 

  
--------------------------------------------------------------------------------
-- Each discrete groupoid is isomorphic to some Δ[ X ]. Specifically,
-- A discrete groupoid category 𝒞 is isomorphic to the discrete groupoid with 
-- the objects of 𝒞 and arrows formed by isomorphism of objects. 

module _ {o} where 
  open Isomorphism (𝐆𝐩𝐝 o o o) using (_≃_ ; _,_ ; morph ; iso)
  open Functor

  discreteCanonicity : ∀ (𝒞 : GroupoidCategory o o o) → 
                        isPreorder (𝒞 .category) →  
                        Σ[ X ∈ Setoid o o ] (𝒞 ≃ Δ[ X ])
  discreteCanonicity 𝒞 pre = 
    obj-setoid , F , F⁻¹ , right-inverse , left-inverse                 
    where 
      open Category (𝒞 .category)
      open Isomorphism (𝒞 .category) using (obj-setoid ; refl-≃)
      F : Functor (𝒞 .category) (Δ[ obj-setoid ] .category)
      F .F₀            = id
      F .fmap f .morph = f
      F .fmap f .iso   = 𝒞 .groupoid .allIso f
      F .F-id          = tt
      F .F-∘ _ _       = tt
      F .F-cong _      = tt 

      F⁻¹ :  Functor (Δ[ obj-setoid ] .category) (𝒞 .category)
      F⁻¹ .F₀             = id
      F⁻¹ .fmap (f , iso) = f
      F⁻¹ .F-id           = refl-≈
      F⁻¹ .F-∘ _ _        = refl-≈
      F⁻¹ .F-cong 
        {f = f , iso-f} 
        {g = g , iso-g} _ = pre .preorder f g 

      right-inverse      : (F ∘F F⁻¹) ≃ₙ IdF
      right-inverse .nat = refl-≃ , λ _ → tt 
      right-inverse .iso = refl-≃ , tt , tt 

      left-inverse      : (F⁻¹ ∘F F) ≃ₙ IdF
      left-inverse .nat = Id , λ _ → idᵣ ⨾ idₗ ⁻¹ 
      left-inverse .iso = Id , idₗ , idₗ 

  