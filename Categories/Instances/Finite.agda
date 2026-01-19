{-# OPTIONS --without-K #-}

module Categories.Instances.Finite where 

open import Categories.Prelude
open import Categories.Category
open import Categories.Functor 
open import Categories.NaturalTransformation

--------------------------------------------------------------------------------
-- Simple finite categories

open PropositionalEquality

--------------------------------------------------------------------------------
-- The empty category 

data Zero {ℓ} : Set ℓ where 

module _ where 
  open Category 
    
  𝟘 : Category o o o 
  𝟘 .Obj = Zero
  𝟘 ._⇒_ _ _ = ⊥ 
  𝟘 ._∘_ () 
  𝟘 .Id {()} 
  𝟘 ._≈_ ()
  𝟘 .eqv .IsEquivalence.refl {()}
  𝟘 .eqv .IsEquivalence.sym {()}
  𝟘 .eqv .IsEquivalence.trans {k = ()}
  𝟘 .idᵣ {f = ()}
  𝟘 .idₗ {f = ()}
  𝟘 .assₗ {h = ()}
  𝟘 ._⋆_ {f = ()}

module _ {ℓ} where 
  open Category (𝟘 {ℓ})

  𝟘-no-objects : ¬ Obj
  𝟘-no-objects () 
  
  𝟘-no-arrows : ∀ (A B : Obj) → ¬ (A ⇒ B) 
  𝟘-no-arrows () 

-- --------------------------------------------------------------------------------
-- -- The category with one object and one arrow

data One : Set where 
  A : One 
 
data _⇒₁_ : One → One → Set where 
  ↻ : A ⇒₁ A  

module _ where 
  open Category 
  𝟙 : Category lzero lzero lzero 
  𝟙 .Obj = One
  𝟙 ._⇒_ X Y = X ⇒₁ Y 
  𝟙 ._∘_ {X} {Y} {Z} ↻ ↻ = ↻ 
  𝟙 .Id {A} = ↻ 
  𝟙 ._≈_ = _≡_ 
  𝟙 .eqv = ≡-equiv 
  𝟙 .idᵣ {f = ↻} = refl 
  𝟙 .idₗ {f = ↻} = refl
  𝟙 .assₗ {A} {D = A} {↻} {↻} {↻} = refl 
  𝟙 ._⋆_ {A} {C = C} refl refl  = refl

module _ where 
  open Category 𝟙 

  𝟙-one-object : ∀ (x y : Obj) → x ≡ y 
  𝟙-one-object A A = refl 
  
  𝟙-one-arrow : ∀ (A : Obj) (f : A ⇒ A) → f ≈ Id -- _≈_ {A} {A} f (Id {A})
  𝟙-one-arrow A ↻ = refl    

--------------------------------------------------------------------------------
-- the category with two objects and one nontrivial arrow: 
--   F0 ------> F1 

data Two : Set where 
  A : Two 
  B : Two 

data _⇒₂_ : Two → Two → Set where 
  ↻ :  ∀ (A : Two) → A ⇒₂ A 
  A↦B : A ⇒₂ B 

module _ where 
  open Category 
  𝟚 : Category lzero lzero lzero 
  𝟚 .Obj = Two  
  𝟚 ._⇒_ X Y = X ⇒₂ Y
  _∘_ 𝟚 {X} {Y} {Z} (↻ .X) (↻ .X) = ↻ X
  _∘_ 𝟚 {X} {Y} {Z} (↻ .B) A↦B = A↦B
  _∘_ 𝟚 {X} {Y} {Z} A↦B (↻ .A) = A↦B
  𝟚 .Id {X} = ↻ X  
  𝟚 ._≈_ = _≡_ 
  𝟚 .eqv = ≡-equiv 
  𝟚 .idᵣ {f = ↻ _} = refl
  𝟚 .idᵣ {f = A↦B} = refl
  𝟚 .idₗ {f = ↻ _} = refl
  𝟚 .idₗ {f = A↦B} = refl
  𝟚 .assₗ {f = ↻ _} {↻ _} {↻ _} = refl
  𝟚 .assₗ {f = ↻ .A} {↻ .A} {A↦B} = refl
  𝟚 .assₗ {f = ↻ .A} {A↦B} {↻ .B} = refl
  𝟚 .assₗ {f = A↦B} {↻ .B} {↻ .B} = refl
  𝟚 ._⋆_ refl refl = refl

module _ where 
  open Category 𝟚 

  allIds : ∀ {X : Two} → (f : X ⇒ X) → f ≡ ↻ X
  allIds {A} (↻ .A) = refl
  allIds {B} (↻ .B) = refl 

  _ : ∀ (f : A ⇒ B) →  f ≡ A↦B 
  _ = λ { A↦B → refl} 

  _ : ∀ (f : B ⇒ B) →  f ≡ ↻ B
  _ = λ { (↻ B) → refl} 

  _ : ¬ (B ⇒ A) 
  _ = λ { () } 

-- --------------------------------------------------------------------------------
-- -- The category with three objects and three non-trivial arrows.
-- {-   
--      B
--      ^  \ 
--      |   \   
--      |    v     
--      A -> C
-- -} 

data Three : Set where 
  A B C : Three 

data _⇒₃_ : Three → Three → Set where 
  ↻ :  ∀ (A : Three) → A ⇒₃ A 
  A↦B : A ⇒₃ B 
  B↦C : B ⇒₃ C
  A↦C : A ⇒₃ C

module _ where 
  open Category 
  𝟛 : Category lzero lzero lzero 
  𝟛 .Obj = Three
  𝟛 ._⇒_ = _⇒₃_
  𝟛 ._∘_ (↻ _) f = f
  𝟛 ._∘_ f (↻ _) = f
  𝟛 ._∘_ B↦C A↦B = A↦C
  𝟛 .Id = ↻ _
  𝟛 ._≈_ = _≡_
  𝟛 .eqv = ≡-equiv
  -- Not sure why Agda can't infer that f ∘ (↻ _) ≡ f until f is destructed.
  𝟛 .idᵣ {f = ↻ _} = refl
  𝟛 .idᵣ {f = A↦B} = refl
  𝟛 .idᵣ {f = B↦C} = refl
  𝟛 .idᵣ {f = A↦C} = refl
  𝟛 .idₗ = refl
  𝟛 .assₗ {f = ↻ _} {↻ _} {↻ _} = refl
  𝟛 .assₗ {f = ↻ .A} {↻ .A} {A↦B} = refl
  𝟛 .assₗ {f = ↻ .B} {↻ .B} {B↦C} = refl
  𝟛 .assₗ {f = ↻ .A} {↻ .A} {A↦C} = refl
  𝟛 .assₗ {f = ↻ .A} {A↦B} {↻ .B} = refl
  𝟛 .assₗ {f = ↻ .A} {A↦B} {B↦C} = refl
  𝟛 .assₗ {f = ↻ .B} {B↦C} {↻ .C} = refl
  𝟛 .assₗ {f = ↻ .A} {A↦C} {↻ .C} = refl
  𝟛 .assₗ {f = A↦B} {↻ .B} {↻ .B} = refl
  𝟛 .assₗ {f = A↦B} {↻ .B} {B↦C} = refl
  𝟛 .assₗ {f = A↦B} {B↦C} {↻ .C} = refl
  𝟛 .assₗ {f = B↦C} {↻ .C} {↻ .C} = refl
  𝟛 .assₗ {f = A↦C} {↻ .C} {↻ .C} = refl
  𝟛 ._⋆_ refl refl = refl 

-- --------------------------------------------------------------------------------
-- Demonstrating a simple functor that is full but not surjective on morphisms

module _ where 
  open Functor 
  ι₂→₃ : Functor 𝟚 𝟛 
  ι₂→₃ .F₀ A = A
  ι₂→₃ .F₀ B = B
  ι₂→₃ .fmap (↻ X) = ↻ (ι₂→₃ .Functor.F₀ X)
  ι₂→₃ .fmap A↦B = A↦B
  ι₂→₃ .F-id = refl
  ι₂→₃ .F-∘ (↻ _) (↻ _) = refl
  ι₂→₃ .F-∘ (↻ .A) A↦B = refl
  ι₂→₃ .F-∘ A↦B (↻ .B) = refl
  ι₂→₃ .F-cong refl = refl

module _ where 
  open Functor ι₂→₃ 

  -- ι₂→₃ is Full, but clearly not surjective on morphisms: 
  -- the arrows ↻ C and B↦C have no corresponding arrows in 𝟚
  -- mapped by ι₂→₃.
  ι₂→₃IsFull : Full ι₂→₃
  ι₂→₃IsFull {A} {A} (↻ .(F₀ A)) = (↻ A) , refl
  ι₂→₃IsFull {A} {B} A↦B = A↦B , refl
  ι₂→₃IsFull {B} {B} (↻ .(F₀ B)) = ↻ B , refl 

  -- ι₂→₃ is also faithful
  ι₂→₃IsFaithful : Faithful ι₂→₃
  ι₂→₃IsFaithful {A} {A} (↻ .A) (↻ .A) eq = refl
  ι₂→₃IsFaithful {A} {B} A↦B A↦B eq = refl
  ι₂→₃IsFaithful {B} {B} (↻ .B) (↻ .B) eq = refl

-- --------------------------------------------------------------------------------
-- Demonstrating a simple functor that is faithful but not injective on morphisms:
-- Map 𝟛 to 𝟚 s.t. A ↦ A , B ↦ B , C ↦ B.

module _ where 
  open Functor 
  γ₃→₂ : Functor 𝟛 𝟚
  γ₃→₂ .F₀ A = A 
  γ₃→₂ .F₀ B = B
  γ₃→₂ .F₀ C = B
  γ₃→₂ .fmap (↻ X) = ↻ (F₀ γ₃→₂ X) 
  γ₃→₂ .fmap A↦B = A↦B
  γ₃→₂ .fmap B↦C = ↻ (F₀ γ₃→₂ B)
  γ₃→₂ .fmap A↦C = A↦B
  γ₃→₂ .F-id = refl
  γ₃→₂ .F-∘ (↻ _) (↻ _) = refl
  γ₃→₂ .F-∘ (↻ .A) A↦B = refl
  γ₃→₂ .F-∘ A↦B (↻ .B) = refl
  γ₃→₂ .F-∘ (↻ .B) B↦C = refl
  γ₃→₂ .F-∘ (↻ .A) A↦C = refl
  γ₃→₂ .F-∘ A↦B B↦C = refl
  γ₃→₂ .F-∘ B↦C (↻ .C) = refl
  γ₃→₂ .F-∘ A↦C (↻ .C) = refl
  γ₃→₂ .F-cong refl = refl

module _ where 
  open Functor γ₃→₂

  -- γ₂→₃ is clearly not injective on arrows: We have 
  --          𝟛          𝟚
  --   -----------------|------
  --  {A↦B , A↦C}      ↦ A↦B 
  --  {B↦B, B↦C, C↦C} ↦ B↦B.
  -- That is, nearly all arrows in 𝟚 are hit by 
  -- multiple arrows in 𝟛. It is faithful, however.
  --   Faithful = ∀ {A B : C.Obj} → (f : A C.⇒ B) 
  --                (g : A C.⇒ B) → 
  --                fmap f ≈ fmap g → 
  --                f C.≈ g 
  -- 𝟛 is a preorder category (each pair of objects
  -- has at most 1 arrow between them), and so trivially,
  -- if both f, g : A ⇒ B, we have f ≈ g.
  γ₃→₂IsFaithful : Faithful γ₃→₂
  γ₃→₂IsFaithful {A} {A} (↻ .A) (↻ .A) eq = refl
  γ₃→₂IsFaithful {A} {B} A↦B A↦B eq = refl
  γ₃→₂IsFaithful {A} {C} A↦C A↦C eq = refl
  γ₃→₂IsFaithful {B} {A} () g eq
  γ₃→₂IsFaithful {B} {B} (↻ .B) (↻ .B) eq = refl
  γ₃→₂IsFaithful {B} {C} B↦C B↦C eq = refl
  γ₃→₂IsFaithful {C} {A} () g eq
  γ₃→₂IsFaithful {C} {B} () g eq
  γ₃→₂IsFaithful {C} {C} (↻ .C) (↻ .C) eq = refl 

  -- γ₂→₃ is not full, in a subtle way: to be full, we must have
  -- for all (F A ⇒ F B) arrows a corresponding (A ⇒ B) arrow.
  --   Full = ∀ {A B : C.Obj} → (g : F₀ A ⇒ F₀ B) → 
  --          Σ[ f ∈ (A C.⇒ B) ] (fmap f ≈ g)
  -- Here, there is an arrow (F C ⇒ F B) = B ⇒ B, namely the 
  -- identity ↻ B. But there is no C ⇒ B arrow!
  γ₃→₂NotFull : ¬ (Full γ₃→₂)
  γ₃→₂NotFull notFull with notFull {C} {B} (↻ B) 
  ... | () 
