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

open import Categories.Instances.Groupoids 
open import Categories.Instances.Cats

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
  Types .category .cong-∘  refl refl = refl
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
  Δ[_] .category .cong-∘  = λ _ _ → tt
  Δ[_] .category .idᵣ  = tt 
  Δ[_] .category .idₗ  = tt
  Δ[_] .category .assₗ  = tt
  Δ[_] .groupoid = Groupoid λ { A∼B → (sym-∼ A∼B) , tt , tt }

  Δ[]IsPreorder : ∀ {e} → isPreorder {e = e}  (Δ[_] .category)
  Δ[]IsPreorder = Preorder  (λ _ _ → tt)

  Δ[]IsDiscrete : isDiscrete {e = e} (Δ[_] .category)
  Δ[]IsDiscrete = Discrete (Δ[_] .groupoid)  Δ[]IsPreorder

--------------------------------------------------------------------------------
-- Δ[ ⊤ ] is terminal in the category of groupoids.

⊤-terminal : isTerminal (Groupoids o o o) (Δ[ ≡-setoid {A = ⊤} ])
⊤-terminal {o = o} = term F λ {𝒞} → unique {𝒞}
  where 
    F : ∀ (𝒞 : GroupoidCategory o o o) → Functor {o₂ = o} {e₂ = o} (𝒞 .category) (Δ[ ≡-setoid {A = ⊤} ] .category)
    F 𝒞 .Functor.F₀ _ =  tt 
    F 𝒞 .Functor.fmap _ = refl 
    F 𝒞 .Functor.F-id = tt 
    F 𝒞 .Functor.F-∘ _ _ = tt 
    F 𝒞 .Functor.F-cong _ = tt 

    unique : ∀ {𝒞 : GroupoidCategory o o o} → (G : Functor (𝒞 .category) (Δ[ ≡-setoid {A = ⊤} ] .category)) → 
                G ≃ₙ (F 𝒞)
    unique G = (refl , λ _ → tt) , refl , tt , tt 

  
--------------------------------------------------------------------------------
-- Each discrete groupoid is isomorphic to some Δ[ X ] 

module _ {o} where 
  open Isomorphism (Groupoids o o o) using (_≃_ ; _,_)

  -- This definition really highlights that I need better tooling for notation
  -- and to possibly reorganize/re-modularize the definitions in Categories.Arrows.
  discreteCanonicity : ∀ (𝒞 : GroupoidCategory o o o) → 
                        isPreorder (𝒞 .category) →  
                        Σ[ X ∈ Setoid o o ] (𝒞 ≃ Δ[ X ])
  discreteCanonicity 𝒞 pre = 
    obj-setoid , {!   !} 
    -- (Func id (λ f → f Isomorphism., 𝒞 .groupoid .allIso f) tt (λ _ _ → tt) (λ _ → tt) , 
    --   IsIso (Func id (λ { (f Isomorphism., iso₁) → f })  refl-≈ (λ _ _ → refl-≈) 
    --     λ { {f = f Isomorphism., iso₁} {g Isomorphism., iso₂} _ → pre .preorder f g }) , 
    --     (Inverse (((Id Isomorphism., (IsIso Id (Inverse idₗ idₗ))) , λ _ → tt) , IsIso refl-≃ (Inverse tt tt)) 
    --     ((Id , λ f → idᵣ ⨾ sym-≈ idₗ) , IsIso Id (Inverse idₗ idₗ))))                        
    where 
      open Category (𝒞 .category)
      open Isomorphism (𝒞 .category) using (obj-setoid ; refl-≃)
  