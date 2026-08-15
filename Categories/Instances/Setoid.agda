{-# OPTIONS --without-K #-}

module Categories.Instances.Setoid where 

open import Categories.Prelude
open import Categories.Category


--------------------------------------------------------------------------------
-- The category of Setoids

module _ where
  open Category 
  open Setoid using (Carrier)
   
  𝐒𝐞𝐭𝐨𝐢𝐝 : ∀ (o e : Level) → Category (lsuc (o ⊔ e)) (o ⊔ e) (o ⊔ e)
  𝐒𝐞𝐭𝐨𝐢𝐝 o e .Obj = Setoid o e 
  𝐒𝐞𝐭𝐨𝐢𝐝 o e ._⇒_ =  _⇉_ 
  𝐒𝐞𝐭𝐨𝐢𝐝 o e ._∘_ = _●_
  𝐒𝐞𝐭𝐨𝐢𝐝 o e .Id = id , id 
  _≈_ (𝐒𝐞𝐭𝐨𝐢𝐝 o e) {A} {B} (f , _) (g , _) =  ∀ (x : A.Carrier) → f x B.≈ g x
    where module A = Setoid A ; module B = Setoid B 
  𝐒𝐞𝐭𝐨𝐢𝐝 o e .eqv {A} {B} .IsEquivalence.refl _ = B .Setoid.refl
  𝐒𝐞𝐭𝐨𝐢𝐝 o e .eqv {A} {B} .IsEquivalence.sym  f~g x = B .Setoid.sym (f~g x)
  𝐒𝐞𝐭𝐨𝐢𝐝 o e .eqv {A} {B} .IsEquivalence.trans f~g g~h x = B .Setoid.trans (f~g x) (g~h x)
  𝐒𝐞𝐭𝐨𝐢𝐝 o e ._⋆_ {C = C} {f = f , _} {h = h , hom-h} {g = g , _} {i = i , _} e₁ e₂ x = 
    C .Setoid.trans (e₁ (g x)) (hom-h (e₂ x))
  𝐒𝐞𝐭𝐨𝐢𝐝 o e .idᵣ {B = B} x = B .Setoid.refl
  𝐒𝐞𝐭𝐨𝐢𝐝 o e .idₗ {B = B} x = B .Setoid.refl
  𝐒𝐞𝐭𝐨𝐢𝐝 o e .assₗ {D = D} x = D .Setoid.refl
