{-# OPTIONS --without-K #-}

module Categories.Prelude.Base where

open import Agda.Primitive public

--------------------------------------------------------------------------------
-- Commonly used agda stdlib modules

open import Data.Nat using (zero ; suc ; ℕ) public
open import Data.Fin renaming 
    (zero to fzero ; suc to fsuc) 
    using (Fin ; toℕ) public
open import Data.Bool hiding (_∨_ ; _∧_) public
open import Data.Product as Product
  renaming (proj₁ to fst ; proj₂ to snd ; _×_ to _*_) 
  using ( _,_  ; ∃ ; ∃-syntax ; Σ ; Σ-syntax ; map₂ ; curry ; uncurry) public
open import Data.Sum
  renaming (_⊎_ to _or_; inj₁ to left; inj₂ to right) 
  hiding (map₂ ; map ; [_,_]) public 
open import Data.Maybe  renaming (map to mapMaybe) hiding (ap) public
open import Data.Empty.Polymorphic using (⊥ ; ⊥-elim) public 
open import Data.Unit.Polymorphic using (⊤ ; tt) public
open import Data.List using 
  (List ; _∷_ ; [] ; map ; reverse) public

open import Function renaming (_∘_ to _○_) using (id ; const ; flip ; _⇔_ ; Equivalence ) public
open import Relation.Binary.Definitions using (Decidable ; DecidableEquality) public
open import Relation.Nullary.Negation using (contradiction; contraposition) public
open import Relation.Nullary using (Dec; yes; no ; map′ ; Irrelevant) public
open import Relation.Nullary.Decidable using (True ; toWitness ; fromWitness) public
open import Relation.Binary using (IsEquivalence ; Substitutive ; Setoid) public

--------------------------------------------------------------------------------
-- generalized variables
variable 
    ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level 
    -- the levels of objects, arrows, and equivalence
    o o₁ o₂ o₃ a a₁ a₂ a₃ e e₁ e₂ e₃ : Level

--------------------------------------------------------------------------------
-- Common functions
private
  variable 
    A B C D : Set ℓ 

cross : (A → C) → (B → D) → A * B → C * D 
cross f g (a , b) = (f a , g b) 

<_,_> : (A → B) → (A → C) → A → B * C 
< f , g > a = f a , g a 

-- Redefining negation to be universe polymorphic
¬_ : (A : Set ℓ) → Set ℓ
¬_ {ℓ} A = A → ⊥ {ℓ}

--------------------------------------------------------------------------------
-- Get the carrier from a setoid 

∣_∣ : Setoid ℓ₁ ℓ₂ → Set ℓ₁ 
∣ s ∣ = s .Setoid.Carrier

--------------------------------------------------------------------------------
-- Pattern synonyms for common Fin constructors

pattern F0 = fzero 
pattern F1 = fsuc F0 
pattern F2 = fsuc F1 
pattern F3 = fsuc F2 
pattern F4 = fsuc F3 
pattern F5 = fsuc F4 
