
module Categories.TypeTheory.STLC.CCCModel where

open import Categories.Prelude hiding (`_) 
open import Categories.Prelude.Equality.Heterogeneous

open import Categories.Category
open import Categories.Constructions.Exponential 
open import Categories.Constructions.Product
open import Categories.Constructions.Terminal
open import Categories.Constructions.CCC

open import Categories.TypeTheory.STLC.Syntax

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

  module Examples where
    λ-id : (τ : Type) → Term ∅ (τ `→ τ) 
    λ-id τ = `λ {τ = τ} (` `0) 

    _ : ⟦ λ-id `⊤ ⟧ tt ≡ id
    _ = refl 