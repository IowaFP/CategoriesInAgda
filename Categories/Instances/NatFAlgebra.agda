{-# OPTIONS --without-K #-}

module Categories.Instances.NatFAlgebra where 

open import Categories.Prelude
open import Categories.Category 
open import Categories.Functor 
open import Categories.NaturalTransformation 

open import Categories.Constructions.FAlgebra hiding (⦅_⦆)
open import Categories.Constructions.Initial

open import Categories.Reasoning.Hom 
open import Categories.Instances.Sets

-- ------------------------------------------------------------------------------
-- The naturals are an initial F-Algebra in the category F-Alg of F-Algebras on Sets.

module NatInitial where 
  open Category (Sets lzero)
  open PropositionalEquality
  open FAlg 
  open Isomorphism (Sets lzero) 
  open Hom 

  NatF : Endofunctor (Sets lzero)
  NatF .Functor.F₀ = λ X → ⊤ {lzero} or X
  NatF .Functor.fmap f (left t) = left t
  NatF .Functor.fmap f (right n) = right (f n)
  NatF .Functor.F-id (left _) = refl 
  NatF .Functor.F-id (right _) = refl 
  NatF .Functor.F-∘ f g (left _) = refl 
  NatF .Functor.F-∘ f g (right _) = refl 
  NatF .Functor.F-cong eq (left _) = refl 
  NatF .Functor.F-cong eq (right n) = cong right (eq n)
  
  open Functor NatF 
  
  AlgCat : Category (lsuc lzero) lzero lzero 
  AlgCat = FAlgebras (Sets lzero) NatF 

  -- We need to leverage Agda data types to construct fixed-points
  data Nat : Set where 
    zero : Nat 
    suc  : Nat → Nat 
  
  -- Likewise we need Agda's recursion to define an initial algebra
  NatIn : FAlg (Sets lzero) NatF
  NatIn = Nat , (λ { (left x) → zero
                   ; (right y) → suc y }) 

  -- Were it not for termination checking, we could instead
  -- write that 
  --   cata (A , φ) n = φ ○ (fmap (cata φ)) ○ NatOut
  -- Instead we'll describe NatOut in terms of cata.
  cata : (φ : FAlg (Sets lzero) NatF) → Nat → φ .Carrier 
  cata (A , φ) zero = φ (left tt)
  cata (A , φ) (suc n) = φ (right (cata (A , φ) n))  

  NatOut : Nat → F₀ Nat 
  NatOut = cata (F₀ Nat , fmap (NatIn .alg))

  -- We confirm that Nat is a fixed-point of F(X) = 1 + X 
  NatIso : (F₀ Nat) ≃ Nat 
  NatIso = φ , NatOut , inv₁ , inv₂
      where 
        open FAlg NatIn renaming (Carrier to A ; alg to φ)
        inv₁ : ∀ (n : Nat) → φ (NatOut n) ≡ n 
        inv₁ zero = refl
        inv₁ (suc n) = cong suc (inv₁ n) 
        inv₂ : ∀ (a : F₀ Nat) → NatOut (φ a) ≡ a 
        inv₂ (left x) = refl
        inv₂ (right y) = cong right (inv₁ y) 

  -- The catamorphism indeed commutes
  ⦅_⦆ : (φ : FAlg (Sets lzero) NatF) → Hom NatIn φ
  ⦅ (A , φ) ⦆ = cata (A , φ) , λ { (left x) → refl
                                 ; (right y) → refl } 
                                  
  -- (Nat , NatIn) is initial in the category of (1 + X)-Algebras
  NatInitial : isInitial AlgCat NatIn 
  NatInitial = init (λ φ → ⦅ φ ⦆) λ { {φ} f → unique φ f }
    where 
      open ≡-Reasoning 
      unique : ∀ (φ : FAlg (Sets lzero) NatF) → (h : Hom NatIn φ) → (n : Nat) → h .hom n ≡ cata φ n
      unique (A , φ) (f , commutes) zero = commutes (left tt)
      unique (A , φ) (f , commutes) (suc n) = begin 
        f (suc n)                  ≡⟨ commutes (right n) ⟩ 
        φ (right (f n))            ≡⟨ cong (φ ○ right) (unique (A , φ) (f , commutes) n) ⟩ 
        φ (right (cata (A , φ) n)) ∎

        