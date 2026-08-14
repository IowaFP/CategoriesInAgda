
module Categories.TypeTheory.STLC.SetModel where

open import Agda.Primitive
open import Function
open import Relation.Binary.PropositionalEquality hiding (J)

open import Categories.TypeTheory.STLC.Syntax

module SetModel where 
  open import Data.Unit 
  open import Data.Product renaming (proj₁ to π₁ ; proj₂ to π₂)

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

  _,,_ : ∀ {ℓ}{A B C : Set ℓ} → 
            (A → B) → 
            (A → C) → 
            A → B × C
  (f ,, g) a = (f a , g a) 

  ε : ∀ {A B : Set} → (A → B) × A → B 
  ε (f , x) = f x 

  ⟦_⟧ : Term Γ τ → ⟦ Γ ⟧ctx → ⟦ τ ⟧t 
  ⟦ ` x ⟧ = ⟦ x ⟧v
  ⟦ `λ {τ = τ} M ⟧ = curry ⟦ M ⟧ 
  ⟦ M · N ⟧  = ε ∘ (⟦ M ⟧ ,, ⟦ N ⟧)
  ⟦ fst M ⟧ = π₁ ∘ ⟦ M ⟧
  ⟦ snd M ⟧ = π₂ ∘ ⟦ M ⟧
  ⟦ ⋆ ⟧ = const tt 
  ⟦ M , N ⟧ = ⟦ M ⟧ ,, ⟦ N ⟧ 