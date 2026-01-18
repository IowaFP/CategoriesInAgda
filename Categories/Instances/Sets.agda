{-# OPTIONS --without-K #-}

module Categories.Instances.Sets where 

open import Data.List.Properties

open import Categories.Prelude
open import Categories.Category
open import Categories.Functor

open import Categories.Constructions.Product
open import Categories.Constructions.Exponential
open import Categories.Constructions.Initial

open PropositionalEquality

--------------------------------------------------------------------------------
-- Set ℓ forms a category on types, which is most closely analogous
-- to the category of sets á la set theory. 

module _ (ℓ : Level) where 
  open Category
  open Functions₁ using (_~_ ; ~-equiv ; ~-setoid)

  Sets : Category (lsuc ℓ) ℓ ℓ
  Sets .Obj = Set ℓ 
  Sets ._⇒_ A B =  A → B 
  Sets ._∘_ f g = f ○ g 
  Sets .Id = id 
  Sets ._≈_ {A = A} {B = B} = _~_ (≡-setoid {_} {B})
  Sets .eqv {A} {B} = ~-equiv (≡-setoid {_} {B})
  Sets .cong-∘ {f = f} {g = g} {i} e₁ e₂ a = trans (cong f (e₂ a)) (e₁ (i a))
  Sets .right-id _ = refl 
  Sets .left-id _ = refl 
  Sets .assₗ _ = refl 

-- -----------------------------------------------------------------------------
-- A note on equality:

private module Problem where 
  -- Because Sets is a *closed category*, the morphisms from A to B can be viewed
  -- as an object in Sets. Thus, for example, (A ⇒ B) = A → B is both an arrow
  -- in Sets and an object. This makes defining extensional equivalence of arrows
  -- problematic, as we could have e.g. B = (X → Y) when defining _≈_:
  --   Sets ._≈_ {A = A} {B = B} = _~_ (≡-setoid {_} {B})
  -- in which case pointwise equivalence is not "deep" enough---we will have that 
  --   f ≈ g 
  -- iff 
  --   ∀ (x : A) → f x ≡ g x, 
  -- where f x and g x have type X → Y. But what we really want is that 
  --   ∀ (x : A) (y : X) → f x y ≡ g x y
  -- (and so forth for arbitrary n-ary functions.)
  -- I'm not sure how to recursively expand the extensional equivalence on 
  -- arbitrary functions. This is problematic when I want to prove that Sets 
  -- admits exponentials, in which case I need to show that the exponential
  -- object (Zʸ, λg) is unique, where λg : X → Y → Z. So I receive a goal of:
  --   λg x ≡ (λ y → g (x , y)) 
  -- where λg x : Y → Z, but what I would really like is the goal:
  --   λg x y ≡ g (x , y)
  -- To demonstrate:
  open Category (Sets lzero)
  problem : ∀ {A B C : Obj} (f g : A ⇒ (B ⇒ C)) → 
            (f ≈ g) ≡ (∀ (x : A) → f x ≡ g x)
  problem f g = refl 

------------------------------------------------------------------------------
-- As an example, List is an Endofunctor on Sets

ListFunctor : Endofunctor (Sets ℓ)
ListFunctor = record 
  { F₀ = List 
  ; fmap = map 
  ; F-id = λ xs → map-id xs 
  ; F-∘ = λ f g xs → map-∘ xs
  ; F-cong = map-cong  }

-- ------------------------------------------------------------------------------
-- initial and terminal objects in Sets

-- ⊤ is a terminal object in Set.
SetTerminal : ∀ {o} → isTerminal (Sets o) ⊤ 
SetTerminal = term (λ _ _ → tt) (λ f a → refl)

-- ⊥ is an initial object in Set.
SetInitial : ∀ {o} → isInitial (Sets o) ⊥ 
SetInitial = init (λ _ ()) λ { _ () }

-------------------------------------------------------------------------
-- _*_ forms products on Sets

open hasProduct  
open AdmitsProducts 

SetsProducts : ∀ ℓ → AdmitsProducts (Sets ℓ) 
SetsProducts _ .products X Y .X₁×X₂ = X * Y
SetsProducts _ .products X Y .`π₁ = fst
SetsProducts _ .products X Y .`π₂ = snd
SetsProducts _ .products X Y .⟨_⨾_⟩ f g x = (f x , g x)
SetsProducts _ .products X Y .project₁ _ = refl 
SetsProducts _ .products X Y .project₂ _ = refl 
SetsProducts _ .products X Y .unique eq₁ eq₂ x = cong₂ _,_ (sym (eq₁ x)) (sym (eq₂ x)) 

-------------------------------------------------------------------------
-- _→_ forms exponentials on Sets

module _ ℓ where 
  open AdmitsProducts (SetsProducts ℓ) 
  open hasExponential
  open AdmitsExponentials
  open import Categories.Prelude.Equality.Extensionality.Propositional
  
  SetsExponentials : AdmitsExponentials (Sets ℓ) (SetsProducts ℓ)
  SetsExponentials .exponentials Z Y .Zʸ = Y → Z 
  SetsExponentials .exponentials Z Y .`eval (f , y) = f y
  SetsExponentials .exponentials Z Y .`λ[_]  f x y = f (x , y)
  SetsExponentials .exponentials Z Y .`transpose g (x , y) = refl
  -- Begrudgingly need extensionality, here. See note above.
  SetsExponentials .exponentials Z Y .`unique g λg λg-exponential x = 
    extensionality (λ y → λg-exponential (x , y)) 