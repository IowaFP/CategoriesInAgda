
module Categories.TypeTheory.STLC.CCCModel where

open import Categories.Prelude
open import Categories.Prelude.Equality.Heterogeneous

open import Categories.Category
open import Categories.Constructions.Exponential 
open import Categories.Constructions.Product
open import Categories.Constructions.Terminal

open import Categories.TypeTheory.STLC.Syntax

-------------------------------------------------------------------------------
-- Modeling the STLC into CCC's


-------------------------------------------------------------------------------
-- There are numerous equivalent definitions of CCC's. We'll 
-- use the straightforward definition of a category that admits products, exponentials,
-- and has a terminal object.

record IsCCC {a o e} (𝒞 : Category o a e) : Set (lsuc a ⊔ lsuc o ⊔ lsuc e)  where 
  open Category 𝒞 

  field 
    products : AdmitsProducts 𝒞
    exponentials : AdmitsExponentials 𝒞 products
    𝕋 : Obj
    isTerm : isTerminal 𝒞 𝕋

  open AdmitsProducts products public 
  open AdmitsExponentials exponentials public 
  open isTerminal isTerm public 

-------------------------------------------------------------------------------
-- An interpretation denotes the syntax of the STLC into a given CCC.

module Interpretation (𝒞 : Category o a e) (ccc : IsCCC 𝒞) where 
  open Category 𝒞 
  open IsCCC ccc

  ⟦_⟧t : Type → Obj 
  ⟦ τ₁ `→ τ₂ ⟧t = ⟦ τ₂ ⟧t ^ ⟦ τ₁ ⟧t 
  ⟦ `⊤ ⟧t = 𝕋
  ⟦ τ₁ `× τ₂ ⟧t = ⟦ τ₁ ⟧t × ⟦ τ₂ ⟧t   
 
  ⟦_⟧ctx : Context → Obj 
  ⟦ ∅ ⟧ctx = 𝕋
  ⟦ Γ , x ⟧ctx = ⟦ Γ ⟧ctx × ⟦ x ⟧t

  ⟦_⟧v : Var Γ τ → ⟦ Γ ⟧ctx ⇒ ⟦ τ ⟧t
  ⟦ `0 ⟧v = `π₂ 
  ⟦ `S x ⟧v = ⟦ x ⟧v ∘ `π₁

  ⟦_⟧ : Term Γ τ → ⟦ Γ ⟧ctx ⇒ ⟦ τ ⟧t 
  ⟦ ` x ⟧ = ⟦ x ⟧v
  ⟦ `λ {τ = τ} M ⟧ = `curry ⟦ M ⟧ 
  ⟦ M · N ⟧  = `eval ∘ ⟨ ⟦ M ⟧ , ⟦ N ⟧ ⟩ 
  ⟦ fst M ⟧ = `π₁ ∘ ⟦ M ⟧
  ⟦ snd M ⟧ = `π₂ ∘ ⟦ M ⟧
  ⟦_⟧ {Γ = Γ} ⋆ = ! ⟦ Γ ⟧ctx 
  ⟦ M , N ⟧ = ⟨ ⟦ M ⟧ , ⟦ N ⟧ ⟩ 

-------------------------------------------------------------------------------
-- Recovering the Set model! 

module SetInterpretation where 
  open import Categories.Instances.Set 
  open PropositionalEquality ; open HeterogeneousEquality

  open Category (𝐒𝐞𝐭 lzero)

  𝐒𝐞𝐭CCC : IsCCC (𝐒𝐞𝐭 lzero)
  𝐒𝐞𝐭CCC .IsCCC.products = (𝐒𝐞𝐭Products lzero)
  𝐒𝐞𝐭CCC .IsCCC.exponentials = (𝐒𝐞𝐭Exponentials lzero)
  𝐒𝐞𝐭CCC .IsCCC.𝕋 = ⊤
  𝐒𝐞𝐭CCC .IsCCC.isTerm = SetTerminal

  open IsCCC 𝐒𝐞𝐭CCC
  open Interpretation (𝐒𝐞𝐭 lzero) 𝐒𝐞𝐭CCC

--   open CCC (𝐒𝐞𝐭 lzero) (𝐒𝐞𝐭Products lzero) (𝐒𝐞𝐭Exponentials lzero) ⊤ SetTerminal
--     renaming 
--       (⟦_⟧t to ⟦_⟧₀t ; 
--        ⟦_⟧v to ⟦_⟧₀v ; 
--        ⟦_⟧ctx to ⟦_⟧₀ctx ; 
--        ⟦_⟧ to ⟦_⟧₀) 


  open import Categories.TypeTheory.STLC.SetModel 
    renaming 
      (⟦_⟧t to ⟦_⟧₁t ; 
       ⟦_⟧v to ⟦_⟧₁v ; 
       ⟦_⟧ctx to ⟦_⟧₁ctx ; 
       ⟦_⟧ to ⟦_⟧₁)   

  same-types : ∀ (τ : Type) → ⟦ τ ⟧t ≡ ⟦ τ ⟧₁t 
  same-types (τ₁ `→ τ₂) = cong₂ (λ X Y → X → Y) (same-types τ₁) (same-types τ₂)
  same-types `⊤ = refl
  same-types (τ₁ `× τ₂) = cong₂ _×_ (same-types τ₁) (same-types τ₂) 
  
  coerce : {A B : Set ℓ} → A ≡ B → A → B 
  coerce refl = id 
  -- This should all go through, modulo some finaggling:
  -- - need extensionality in `λ case 
  -- - We have naming overlaps on `fst` and `snd`
-- - Heterogeneous equality is a pain for relating  f x ≅ g y
  same-terms : ∀ (M : Term Γ τ) 
           (H₀ : ⟦ Γ ⟧ctx)
           (H₁ : ⟦ Γ ⟧₁ctx) → 
           ({τ′ : Type} (x : Var Γ τ′) → ⟦ x ⟧v H₀ ≅ ⟦ x ⟧₁v H₁) → 
           (⟦ M ⟧ H₀) ≅ ⟦ M ⟧₁ H₁ 
  same-terms (` x) H₀ H₁ V = V x
  same-terms (`λ M) H₀ H₁ V = {! same-terms M   !}
  same-terms (M Term.· M₁) H₀ H₁ V = {! same-terms M H₀ H₁ V   !}
  same-terms (Term.fst M) H₀ H₁ V = {! cong  !}
  same-terms (Term.snd M) H₀ H₁ V = {!   !}
  same-terms (M , N) H₀ H₁ V = ? -- 
  same-terms ⋆ H₀ H₁ V = refl 