
module Categories.TypeTheory.STLC.CCCModel where

open import Categories.Prelude
open import Categories.TypeTheory.STLC.Syntax

-- TODO!

-- module CCC where 
--   private
--     variable
--       ℓ ℓ₁ ℓ₂ : Level 

--   record CCC : Set (lsuc ℓ) where 
--     -- Category attributes
--     infixr 4 _⇒_
--     field 
--       Obj : Set ℓ 
--       _⇒_ : Obj → Obj → Set ℓ
--       _○_ : ∀ {A B C : Obj} → B ⇒ C → A ⇒ B → A ⇒ C 
--       -- The identity arrow on object A
--       Id : ∀ {A}  → A ⇒ A
  
--     -- Terminal object 
--     field 
--       ⊤ : Obj 
--       ! : ∀ (A : Obj) → A ⇒ ⊤ 

--     -- Products  
--     infixr 5 _×_ 
--     field
--       _×_ : Obj → Obj → Obj
--       π₁ : {A B : Obj} → A × B ⇒ A 
--       π₂ : {A B : Obj} → A × B ⇒ B
--       ⟨_,_⟩ : {A B C : Obj} → A ⇒ B → A ⇒ C → A ⇒ B × C 
    
--     -- exponentials
--     infixr 3 _—→_ 
--     field 
--       _—→_ : (Z Y : Obj) → Obj 
--       `eval : ∀ {Z Y : Obj} → (Y —→ Z) × Y ⇒ Z 
--       `curry : ∀ {X Y Z : Obj} → X × Y ⇒ Z → X ⇒ (Y —→ Z) 

--   module CCCModel {ℓ} (𝒞 : CCC {ℓ}) where 
--     open CCC 𝒞 
--     open Syntax 

--     ⟦_⟧t : Type → Obj 
--     ⟦ τ₁ `→ τ₂ ⟧t = ⟦ τ₁ ⟧t —→ ⟦ τ₂ ⟧t
--     ⟦ `⊤ ⟧t = ⊤
--     ⟦ τ₁ `× τ₂ ⟧t = ⟦ τ₁ ⟧t × ⟦ τ₂ ⟧t   
 
--     ⟦_⟧ctx : Context → Obj 
--     ⟦ ∅ ⟧ctx = ⊤
--     ⟦ Γ , x ⟧ctx = ⟦ Γ ⟧ctx × ⟦ x ⟧t

--     ⟦_⟧v : Var Γ τ → ⟦ Γ ⟧ctx ⇒ ⟦ τ ⟧t
--     ⟦ `0 ⟧v = π₂ 
--     ⟦ `S x ⟧v = ⟦ x ⟧v ○ π₁

--     ⟦_⟧ : Term Γ τ → ⟦ Γ ⟧ctx ⇒ ⟦ τ ⟧t 
--     ⟦ ` x ⟧ = ⟦ x ⟧v
--     ⟦ `λ {τ = τ} M ⟧ = `curry ⟦ M ⟧ 
--     ⟦ M · N ⟧  = `eval ○ ⟨ ⟦ M ⟧ , ⟦ N ⟧ ⟩ 
--     ⟦ fst M ⟧ = π₁ ○ ⟦ M ⟧
--     ⟦ snd M ⟧ = π₂ ○ ⟦ M ⟧
--     ⟦_⟧ {Γ = Γ} ⋆ = ! ⟦ Γ ⟧ctx 
--     ⟦ M , N ⟧ = ⟨ ⟦ M ⟧ , ⟦ N ⟧ ⟩ 
