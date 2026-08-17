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
  `S_ : Var Γ υ → Var (Γ , τ) υ

data Term : Context → Type → Set where 
  ` : Var Γ τ → Term Γ τ 
  `λ : Term (Γ , τ) υ → Term Γ (τ `→ υ)
  _·_ : Term Γ (τ `→ υ) → Term Γ τ → Term Γ υ 
  fst : Term Γ (τ `× υ) → Term Γ τ 
  snd : Term Γ (τ `× υ) → Term Γ υ 
  _,_ : Term Γ τ → Term Γ υ → Term Γ (τ `× υ) 
  ⋆ : Term Γ `⊤

-------------------------------------------------------------------------------
-- Renaming

Renaming : ∀ (Γ Δ : Context) → Set 
Renaming Γ Δ = ∀ {τ} → Var Γ τ → Var Δ τ 

lift : Renaming Γ Δ → Renaming (Γ , τ) (Δ , τ)
lift ρ `0 = `0
lift ρ (`S v) = `S (ρ v) 

ren : Renaming Γ Δ → Term Γ τ → Term Δ τ 
ren ρ (` x) = ` (ρ x)
ren ρ (`λ M) = `λ (ren (lift ρ) M)
ren ρ (M · N) = ren ρ M · ren ρ N
ren ρ (fst M) = fst (ren ρ M)
ren ρ (snd M) = snd (ren ρ M)
ren ρ (M , N) = ren ρ M , ren ρ N
ren ρ ⋆ = ⋆ 

-------------------------------------------------------------------------------
-- Substitution
 
Substitution : ∀ (Γ Δ : Context) → Set 
Substitution Γ Δ = ∀ {τ} → Var Γ τ → Term Δ τ 

lifts : Substitution Γ Δ → Substitution (Γ , τ) (Δ , τ)
lifts σ `0 = ` `0 
lifts σ (`S v) = ren `S_ (σ v)

sub : Substitution Γ Δ → Term Γ τ → Term Δ τ 
sub σ (` x) = (σ x)
sub σ (`λ M) = `λ (sub (lifts σ) M)
sub σ (M · N) = sub σ M · sub σ N
sub σ (fst M) = fst (sub σ M)
sub σ (snd M) = snd (sub σ M)
sub σ (M , N) = sub σ M , sub σ N
sub σ ⋆ = ⋆ 

-- Identity substitution
idSub : Substitution Γ Γ 
idSub = `

-- Extending a substitution 
extend : Substitution Γ Δ → Term Γ τ → Substitution (Γ , τ) Δ 
extend σ M `0 = sub σ M
extend σ M (`S x) = σ x  

-- beta substitution
_β[_] : Term (Γ , τ) υ → Term Γ τ → Term Γ υ
M β[ N ] = sub (extend idSub N) M 