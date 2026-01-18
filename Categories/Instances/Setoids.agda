{-# OPTIONS --without-K #-}

module Categories.Instances.Setoids where 

open import Categories.Prelude
open import Categories.Category


--------------------------------------------------------------------------------
-- The category of Setoids 

module _ where
  open Category 
  open Setoid using (Carrier)

  record _⇒ₛ_ (𝒜 : Setoid o₁ e₁) (ℬ : Setoid o₂ e₂) : Set (lsuc o₁ ⊔ lsuc o₂ ⊔ e₁ ⊔ e₂) where 
    constructor _,_
    private module A = Setoid 𝒜 
    private module B = Setoid ℬ
    field 
      f : A.Carrier → B.Carrier 
      hom : ∀ {x y : A.Carrier} → x A.≈ y → f x B.≈ f y

  -- Setoid arrow composition
  _●_ : ∀ {A B C : Setoid o e} → B ⇒ₛ C → A ⇒ₛ B → A ⇒ₛ C 
  (f , hom-f) ● (g , hom-g) = (f ○ g) , hom-f ○ hom-g

  Setoids : ∀ (o e : Level) → Category (lsuc o ⊔ lsuc e) (lsuc o ⊔ e) (o ⊔ e)
  Setoids o e .Obj = Setoid o e 
  Setoids o e ._⇒_ =  _⇒ₛ_ 
  Setoids o e ._∘_ = _●_
  Setoids o e .Id = id , id 
  _≈_ (Setoids o e) {A} {B} (f , _) (g , _) =  ∀ (x : A.Carrier) → f x B.≈ g x
    where private module A = Setoid A ; private module B = Setoid B 
  Setoids o e .eqv {A} {B} .IsEquivalence.refl _ = B .Setoid.refl
  Setoids o e .eqv {A} {B} .IsEquivalence.sym  f~g x = B .Setoid.sym (f~g x)
  Setoids o e .eqv {A} {B} .IsEquivalence.trans f~g g~h x = B .Setoid.trans (f~g x) (g~h x)
  Setoids o e .cong-∘ {C = C} {f = f , _} {h = h , hom-h} {g = g , _} {i = i , _} e₁ e₂ x = 
    C .Setoid.trans (e₁ (g x)) (hom-h (e₂ x))
  Setoids o e .right-id {B = B} x = B .Setoid.refl
  Setoids o e .left-id {B = B} x = B .Setoid.refl
  Setoids o e .assₗ {D = D} x = D .Setoid.refl
