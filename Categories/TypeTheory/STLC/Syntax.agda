module Categories.TypeTheory.STLC.Syntax where

open import Agda.Primitive
open import Function
open import Relation.Binary.PropositionalEquality hiding (J)

-------------------------------------------------------------------------------
-- Syntax of the STLC with unit and products

data Type : Set where 
    _`→_ : Type → Type → Type 
    `⊤ : Type 
    _`×_ : Type → Type → Type 

variable 
  τ υ : Type 

data Context : Set where 
  ∅ : Context 
  _,_ : Context → Type → Context

variable 
  Γ Δ : Context

data Var : Context → Type → Set where 
  `0 : Var (Γ , τ) τ 
  `S : Var Γ υ → Var (Γ , τ) υ

data Term : Context → Type → Set where 
  ` : Var Γ τ → Term Γ τ 
  `λ : Term (Γ , τ) υ → Term Γ (τ `→ υ)
  _·_ : Term Γ (τ `→ υ) → Term Γ τ → Term Γ υ 
  fst : Term Γ (τ `× υ) → Term Γ τ 
  snd : Term Γ (τ `× υ) → Term Γ υ 
  _,_ : Term Γ τ → Term Γ υ → Term Γ (τ `× υ) 
  ⋆ : Term Γ `⊤
