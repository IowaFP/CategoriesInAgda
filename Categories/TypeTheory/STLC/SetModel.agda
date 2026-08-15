
module Categories.TypeTheory.STLC.SetModel where

open import Agda.Primitive
open import Categories.Prelude renaming (_○_ to _∘_ ; fst to π₁ ; snd to π₂ ; _*_ to _×_)
open import Categories.TypeTheory.STLC.Syntax

-------------------------------------------------------------------------------
-- The model in Set, which is a CCC

⟦_⟧t : Type → Set 
⟦ τ₁ `→ τ₂ ⟧t = ⟦ τ₁ ⟧t → ⟦ τ₂ ⟧t
⟦ `⊤ ⟧t = ⊤
⟦ τ₁ `× τ₂ ⟧t = ⟦ τ₁ ⟧t × ⟦ τ₂ ⟧t 

⟦_⟧ctx : Context → Set 
⟦ ∅ ⟧ctx = ⊤
⟦ Γ , x ⟧ctx = ⟦ Γ ⟧ctx × ⟦ x ⟧t 

⟦_⟧v : Var Γ τ → ⟦ Γ ⟧ctx → ⟦ τ ⟧t 
⟦ `0 ⟧v = π₂ 
⟦ `S x ⟧v = ⟦ x ⟧v ∘ π₁

ε : ∀ {A B : Set} → (A → B) × A → B 
ε (f , x) = f x 

⟦_⟧ : Term Γ τ → ⟦ Γ ⟧ctx → ⟦ τ ⟧t 
⟦ ` x ⟧ = ⟦ x ⟧v
⟦ `λ {τ = τ} M ⟧ = curry ⟦ M ⟧ 
⟦ M · N ⟧  = ε ∘ < ⟦ M ⟧ , ⟦ N ⟧ > 
⟦ fst M ⟧ = π₁ ∘ ⟦ M ⟧
⟦ snd M ⟧ = π₂ ∘ ⟦ M ⟧
⟦ ⋆ ⟧ = const tt 
⟦ M , N ⟧ = < ⟦ M ⟧ , ⟦ N ⟧ > 