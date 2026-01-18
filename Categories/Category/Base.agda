{-# OPTIONS --without-K #-}

module Categories.Category.Base where 

open import Categories.Prelude

--------------------------------------------------------------------------------
-- Defining a category

record Category (o a e : Level) : Set (lsuc (o ⊔ a ⊔ e)) where 
    constructor Cat
    infixr 5 _⇒_ 
    infixl 5 _∘_
    infixl 0 _≈_

    field
      -- The types of objects, arrows, and composition
      Obj : Set o
      _⇒_ : Obj → Obj → Set a
      _∘_ : ∀ {A B C : Obj} → B ⇒ C → A ⇒ B → A ⇒ C 

      -- The identity arrow on object A
      Id : ∀ {A}  → A ⇒ A 

      -- Setoid equality
      _≈_ : ∀ {A B} → A ⇒ B → A ⇒ B → Set e
      eqv : ∀ {A B} → IsEquivalence (_≈_ {A} {B})

      -- laws 
      right-id : ∀ {A B} {f : A ⇒ B} → f ∘ Id ≈ f 
      left-id : ∀ {A B} {f : A ⇒ B} → Id ∘ f ≈ f 
      assₗ : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} →  
              h ∘ (g ∘ f) ≈ (h ∘ g) ∘ f
      cong-∘  : ∀ {A B C} {f h : B ⇒ C} {g i : A ⇒ B} → 
                  f ≈ h → g ≈ i → f ∘ g ≈ h ∘ i        
     
    module _ {A B : Obj} where
      open IsEquivalence (eqv {A} {B}) renaming 
        (refl to refl-≈ ; 
         sym to sym-≈ ; 
         trans to trans-≈ ; 
         reflexive to respects) public 

    -- The setoid of morphisms and their equality types
    hom-setoid : Obj → Obj → Setoid _ _
    hom-setoid A B = record
      { Carrier       = A ⇒ B
      ; _≈_           = _≈_
      ; isEquivalence = eqv {A} {B} 
      }

    -- congruence on left of a composition
    cong-∘ₗ : ∀ {A B C} {f h : B ⇒ C} {g : A ⇒ B} → f ≈ h → f ∘ g ≈ h ∘ g
    cong-∘ₗ pf = cong-∘ pf refl-≈

    -- congruence on right of a composition
    cong-∘ᵣ : ∀ {A B C} {f h : A ⇒ B} {g : B ⇒ C} → f ≈ h → g ∘ f ≈ g ∘ h
    cong-∘ᵣ pf = cong-∘ refl-≈ pf              
    
    -- reassociate from left *to right*
    assᵣ : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} →  
                (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
    assᵣ = sym-≈ assₗ

    -- Infix notation for transitivity; emphasizes that
    -- transitivity is composition on the groupoid model of identity types.
    infixr 3 _⨾_ 
    _⨾_ : ∀ {A B} {f g h : A ⇒ B} → f ≈ g → g ≈ h → f ≈ h
    _⨾_ = trans-≈ 
    
    -- opposite category
    op : Category o a e 
    op .Obj = Obj 
    op ._⇒_ A B = B ⇒ A
    op ._∘_ = λ f g → g ∘ f
    op .Id = Id 
    op ._≈_ = _≈_
    op .eqv = eqv 
    op .right-id = left-id
    op .left-id = right-id
    op .assₗ = assᵣ
    op .cong-∘ e₁ e₂ = cong-∘ e₂ e₁  


    
--------------------------------------------------------------------------------
-- Properties and definitions on a given category 𝒞

module _ (𝒞 : Category o a e) where 
  open Category 𝒞 
  private
    variable 
      A B C : Obj 
  
  infixr 5 _[_,_] 
  infixr 5 _[_≈_] 
  infixr 5 _[_∘_] 

  -- Accessor for arrow types when category is unopened
  _[_,_] : Obj → Obj → Set a 
  _[_,_] A B = A ⇒ B

  -- For equating arrows when category is unopened
  _[_≈_] : (A ⇒ B) → (A ⇒ B) → Set e 
  _[_≈_] = _≈_

  -- Accessor for composition when category is unopened
  _[_∘_] : (B ⇒ C) → (A ⇒ B) → (A ⇒ C) 
  _[_∘_] = _∘_

-- --------------------------------------------------------------------------------
-- -- Alternative infix syntax (To use e.g. when one has two categorys 𝒞 and 𝒟 in scope)

module `-Syntax (𝒞 : Category o a e) where
  open Category 𝒞 renaming (_⇒_ to _`⇒_ ; _∘_ to _`∘_ ; Id to `Id ; _≈_ to _`≈_) public
      