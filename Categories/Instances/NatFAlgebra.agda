{-# OPTIONS --without-K #-}

module Categories.Instances.NatFAlgebra where 

open import Categories.Prelude
open import Categories.Category 
open import Categories.Functor 
open import Categories.NaturalTransformation 

open import Categories.Constructions.FAlgebra hiding (⦅_⦆)
open import Categories.Constructions.Initial

open import Categories.Reasoning.Hom 
open import Categories.Instances.Set

-- ------------------------------------------------------------------------------
-- The naturals are an initial F-Algebra in the category F-Alg of F-Algebras on 𝐒𝐞𝐭.

module NatInitial where 
  open Category (𝐒𝐞𝐭 lzero)
  open PropositionalEquality
  open FAlg 
  open Isomorphism (𝐒𝐞𝐭 lzero) 
  open AlgHom 

  NatF : Endofunctor (𝐒𝐞𝐭 lzero)
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
  AlgCat = FAlgebras (𝐒𝐞𝐭 lzero) NatF 

  -- We need to leverage Agda data types to construct fixed-points,
  -- and to leverage Agda's recursion to define an initial algebra
  ℕIn : FAlg (𝐒𝐞𝐭 lzero) NatF
  ℕIn = ℕ , (λ { (left x) → zero
                   ; (right y) → suc y }) 

  -- Were it not for termination checking, we could instead
  -- write that 
  --   cata (A , φ) n = φ ○ (fmap (cata φ)) ○ ℕOut
  -- Instead we'll describe ℕOut in terms of cata.
  cata : (φ : FAlg (𝐒𝐞𝐭 lzero) NatF) → ℕ → φ .Carrier 
  cata (A , φ) zero = φ (left tt)
  cata (A , φ) (suc n) = φ (right (cata (A , φ) n))  

  ℕOut : ℕ → F₀ ℕ 
  ℕOut = cata (F₀ ℕ , fmap (ℕIn .alg))

  -- We confirm that ℕ is a fixed-point of F(X) = 1 + X 
  ℕIso : (F₀ ℕ) ≃ ℕ 
  ℕIso = φ , ℕOut , inv₁ , inv₂
      where 
        open FAlg ℕIn renaming (Carrier to A ; alg to φ)
        inv₁ : ∀ (n : ℕ) → φ (ℕOut n) ≡ n 
        inv₁ zero = refl
        inv₁ (suc n) = cong suc (inv₁ n) 
        inv₂ : ∀ (a : F₀ ℕ) → ℕOut (φ a) ≡ a 
        inv₂ (left x) = refl
        inv₂ (right y) = cong right (inv₁ y) 

  -- The catamorphism indeed commutes
  ⦅_⦆ : (φ : FAlg (𝐒𝐞𝐭 lzero) NatF) → AlgHom ℕIn φ
  ⦅ (A , φ) ⦆ = cata (A , φ) , λ { (left x) → refl
                                 ; (right y) → refl } 
                                  
  -- (ℕ , ℕIn) is initial in the category of (1 + X)-Algebras
  ℕInitial : isInitial AlgCat ℕIn 
  ℕInitial = init (λ φ → ⦅ φ ⦆) λ { {φ} f → unique φ f }
    where 
      open ≡-Reasoning 
      unique : ∀ (φ : FAlg (𝐒𝐞𝐭 lzero) NatF) → (h : AlgHom ℕIn φ) → 
                 (n : ℕ) → h .hom n ≡ cata φ n
      unique (A , φ) (f , commutes) zero = commutes (left tt)
      unique (A , φ) (f , commutes) (suc n) = begin 
        f (suc n)                  ≡⟨ commutes (right n) ⟩ 
        φ (right (f n))            ≡⟨ cong (φ ○ right) (unique (A , φ) (f , commutes) n) ⟩ 
        φ (right (cata (A , φ) n)) ∎

        