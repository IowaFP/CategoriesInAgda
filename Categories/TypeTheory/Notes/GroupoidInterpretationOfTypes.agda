{-# OPTIONS --without-K #-}
module Categories.TypeTheory.Notes.GroupoidInterpretationOfTypes where

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
  Types : Category o o o 
  Types .Obj = A
  Types ._⇒_ a b = a ≡ b
  Types ._∘_ = flip trans
  Types .Id = refl
  Types ._≈_  = _≡_ 
  Types .eqv .IsEquivalence.refl = refl
  Types .eqv .IsEquivalence.sym  = sym
  Types .eqv .IsEquivalence.trans  = trans
  Types ._⋆_  refl refl = refl
  Types .idᵣ  = refl 
  Types .idₗ {f = refl} = refl 
  Types .assₗ {f = refl} {refl} {refl} = refl

  TypesIsGroupoid : isGroupoid Types
  TypesIsGroupoid refl =  refl , refl , refl 

--------------------------------------------------------------------------------
-- The UIP is equivalent to the statement that Types is discrete (recall 
-- that a discrete category is a preorder groupoid.)
-- The translation is immediate.

  UIP : Set o  
  UIP = ∀ {a b : A} → (p q : a ≡ b) → p ≡ q 

  UIP⇔Preorder : UIP ⇔ isPreorder Types 
  UIP⇔Preorder .to        = id 
  UIP⇔Preorder .from      = id 
  UIP⇔Preorder .to-cong   = id
  UIP⇔Preorder .from-cong = id

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

  Δ[_] : Category ℓ₁ ℓ₂ e 
  Δ[_] .Obj = Carrier
  Δ[_] ._⇒_ = _∼_
  Δ[_] ._∘_ = flip trans-∼ 
  Δ[_] .Id = refl-∼
  Δ[_] ._≈_  _ _ = ⊤ 
  Δ[_] .eqv .IsEquivalence.refl = tt
  Δ[_] .eqv .IsEquivalence.sym  = λ _ → tt 
  Δ[_] .eqv .IsEquivalence.trans  = λ _ _ → tt
  Δ[_] ._⋆_  = λ _ _ → tt
  Δ[_] .idᵣ  = tt 
  Δ[_] .idₗ  = tt
  Δ[_] .assₗ  = tt

  Δ[]IsGroupoid : isGroupoid {e = e} Δ[_]
  Δ[]IsGroupoid A∼B = sym-∼ A∼B , tt , tt

  Δ[]IsPreorder : isPreorder {e = e}  Δ[_]
  Δ[]IsPreorder  _ _ = tt

  Δ[]IsDiscrete : isDiscrete {e = e} Δ[_]
  Δ[]IsDiscrete = Δ[]IsGroupoid , Δ[]IsPreorder

--------------------------------------------------------------------------------
-- Δ[ ⊤ ] is terminal in the category of groupoids.

⊤-terminal : isTerminal (𝐆𝐩𝐝 o o o) (Δ[ ` ⊤ ] , Δ[]IsGroupoid (` ⊤))
⊤-terminal {o = o} = term F λ {𝒞} → unique {𝒞}
  where 
    open Functor 
    F : ∀ (𝒞 : GroupoidCategory o o o) → 
           𝒞 .category ⇛ Δ[ ` ⊤ ]
    F 𝒞 .F₀ _ =  tt 
    F 𝒞 .fmap _ = refl 
    F 𝒞 .F-id = tt 
    F 𝒞 .F-∘ _ _ = tt 
    F 𝒞 .F-cong _ = tt 

    unique : ∀ {𝒞 : GroupoidCategory o o o} → 
                (G : 𝒞 .category ⇛ Δ[ ` ⊤ ]) → 
                G ≃ₙ F 𝒞
    unique G = (refl , λ _ → tt) , refl , tt , tt 

  
--------------------------------------------------------------------------------
-- Each discrete groupoid is isomorphic to some Δ[ X ]. Specifically,
-- A discrete groupoid category 𝒞 is isomorphic to the discrete groupoid with 
-- the objects of 𝒞 and arrows formed by isomorphism of objects. 

module _ {o} where 
  open Isomorphism (𝐂𝐚𝐭 o o o) using (_≃_ ; _,_ ; morph ; iso)
  open Isomorphism using (Objs ; refl-≃)
  open Functor

  discreteCanonicity : ∀ (𝒞 : Category o o o) → 
                         (d : isDiscrete 𝒞) → 
                         Σ[ X ∈ Setoid o o ] (𝒞 ≃ Δ[ X ])
  discreteCanonicity 𝒞 d = 
    Objs(𝒞) , F , F⁻¹ , right-inverse , left-inverse                 
    where 
      open Category 𝒞
      F : 𝒞 ⇛ Δ[ Objs(𝒞) ]
      F .F₀            = id
      F .fmap f        = f Isomorphism., d .groupoid f
      F .F-id          = tt
      F .F-∘ _ _       = tt
      F .F-cong _      = tt 

      F⁻¹ :  Δ[ Objs(𝒞) ] ⇛ 𝒞
      F⁻¹ .F₀             = id
      F⁻¹ .fmap (f , iso) = f
      F⁻¹ .F-id           = refl-≈
      F⁻¹ .F-∘ _ _        = refl-≈
      F⁻¹ .F-cong 
        {f = f , iso-f} 
        {g = g , iso-g} _ = d .preorder f g

      right-inverse      : (F ∘F F⁻¹) ≃ₙ IdF
      right-inverse .nat = refl-≃ 𝒞 , λ _ → tt 
      right-inverse .iso = refl-≃ 𝒞 , tt , tt 

      left-inverse      : (F⁻¹ ∘F F) ≃ₙ IdF
      left-inverse .nat = Id , λ _ → idᵣ ⨾ idₗ ⁻¹ 
      left-inverse .iso = Id , idₗ , idₗ 

  