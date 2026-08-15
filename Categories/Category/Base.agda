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
    infixr 7 _⋆_

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
      idᵣ : ∀ {A B} {f : A ⇒ B} → f ∘ Id ≈ f 
      idₗ : ∀ {A B} {f : A ⇒ B} → Id ∘ f ≈ f 
      assₗ : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} →  
              h ∘ (g ∘ f) ≈ (h ∘ g) ∘ f
      -- congruence. The notation is borrowed from HoTT book
      -- (Ch 2.1) and denotes horizontal composition of 
      -- arrows (viewing arrow equivalence as paths)
      _⋆_  : ∀ {A B C} {f h : B ⇒ C} {g i : A ⇒ B} → 
                  f ≈ h → g ≈ i → f ∘ g ≈ h ∘ i        
     
    module _ {A B : Obj} where
      open IsEquivalence (eqv {A} {B}) renaming 
        (refl to refl-≈ ; 
         sym to sym-≈ ; 
         trans to trans-≈ ; 
         reflexive to respects) public 

    -- The setoid of morphisms and morphism equivalence
    Hom : Obj * Obj → Setoid _ _
    Hom (A , B) = record
      { Carrier       = A ⇒ B
      ; _≈_           = _≈_ 
      ; isEquivalence = eqv {A} {B} 
      } 
    
    -- Infix notation for transitivity; emphasizes that
    -- transitivity is composition
    instance 
      gpd : ∀ {A B : Obj} → GroupoidSyntax (_≈_ {A} {B})
      gpd = Groupoid refl-≈ sym-≈ trans-≈ 

    -- congruence on left of a composition (Whiskering)
    infixl 7 _⋆ₗ_ _⋆ᵣ_ 
    _⋆ₗ_ : ∀ {A B C} {f h : B ⇒ C} → f ≈ h → (g : A ⇒ B) → f ∘ g ≈ h ∘ g
    pf ⋆ₗ g = pf ⋆ refl-≈

    -- congruence on right of a composition (Whiskering)
    _⋆ᵣ_ : ∀ {A B C} {f h : A ⇒ B} (g : B ⇒ C) → f ≈ h → g ∘ f ≈ g ∘ h
    g ⋆ᵣ pf = refl-≈ ⋆ pf              
    
    -- reassociate from left *to right*
    assᵣ : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} →  
                (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
    assᵣ = assₗ ⁻¹
    
    -- opposite category
    op : Category o a e 
    op .Obj = Obj 
    op ._⇒_ A B = B ⇒ A
    op ._∘_ = λ f g → g ∘ f
    op .Id = Id 
    op ._≈_ = _≈_
    op .eqv = eqv 
    op .idᵣ = idₗ
    op .idₗ = idᵣ
    op .assₗ = assᵣ
    op ._⋆_ e₁ e₂ = e₂ ⋆ e₁

    


    
--------------------------------------------------------------------------------
-- Properties and definitions on a given category 𝒞

module _ (𝒞 : Category o a e) where 
  open Category 𝒞 
  private
    variable 
      A B C : Obj 
  
  _ᵒᵖ = op 

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

module `Category (𝒞 : Category o a e) where
  open Category 𝒞 
    renaming (Obj to `Obj ; 
              _⇒_ to _`⇒_ ; 
              _∘_ to _`∘_ ; 
              Id to `Id ; 
              _≈_ to _`≈_ ; 
              eqv to `eqv ;
              idᵣ to `idᵣ ; 
              idₗ to `idₗ ; 
              assₗ to `assₗ ; 
              _⋆_ to _`⋆_ ; 
              refl-≈ to `refl-≈ ;
              sym-≈ to `sym-≈ ;
              trans-≈ to `trans-≈ ;
              Hom to `Hom ;
              _⋆ₗ_ to _`⋆ₗ_ ;
              _⋆ᵣ_ to _`⋆ᵣ_ ;
              assᵣ to `assᵣ ;
              op to `op) public
      