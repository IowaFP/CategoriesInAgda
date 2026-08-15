{-# OPTIONS --without-K #-}

module Categories.Instances.Set where 

open import Data.List.Properties

open import Categories.Prelude
open import Categories.Category
open import Categories.Functor

open import Categories.Constructions.Product
open import Categories.Constructions.Exponential
open import Categories.Constructions.Initial
open import Categories.Constructions.Terminal

open PropositionalEquality

--------------------------------------------------------------------------------
-- Set ℓ forms a category on types, which is most closely analogous
-- to the category of sets á la set theory. 

module _ (ℓ : Level) where 
  open Category
  open Functions₁ using (_~_ ; ~-equiv ; ~-setoid)
  
  𝐒𝐞𝐭 : Category (lsuc ℓ) ℓ ℓ
  𝐒𝐞𝐭 .Obj = Set ℓ 
  𝐒𝐞𝐭 ._⇒_ A B =  A → B 
  𝐒𝐞𝐭 ._∘_ f g = f ○ g 
  𝐒𝐞𝐭 .Id = id 
  𝐒𝐞𝐭 ._≈_ {A = A} {B = B} = _∼_
  𝐒𝐞𝐭 .eqv {A} {B} = ∼-equiv
  𝐒𝐞𝐭 ._⋆_ {f = f} {g = g} {i} e₁ e₂ a = trans (cong f (e₂ a)) (e₁ (i a))
  𝐒𝐞𝐭 .idᵣ _ = refl 
  𝐒𝐞𝐭 .idₗ _ = refl 
  𝐒𝐞𝐭 .assₗ _ = refl 

-- -----------------------------------------------------------------------------
-- A note on equality:

private module Problem where 
  -- Because 𝐒𝐞𝐭 is a *closed category*, the morphisms from A to B can be viewed
  -- as an object in 𝐒𝐞𝐭. Thus, for example, (A ⇒ B) = A → B is both an arrow
  -- in 𝐒𝐞𝐭 and an object. This makes defining extensional equivalence of arrows
  -- problematic, as we could have e.g. B = (X → Y) when defining _≈_:
  --   𝐒𝐞𝐭 ._≈_ {A = A} {B = B} = _~_ (` B)
  -- in which case pointwise equivalence is not "deep" enough---we will have that 
  --   f ≈ g 
  -- iff 
  --   ∀ (x : A) → f x ≡ g x, 
  -- where f x and g x have type X → Y. But what we really want is that 
  --   ∀ (x : A) (y : X) → f x y ≡ g x y
  -- (and so forth for arbitrary n-ary functions.)
  -- I'm not sure how to recursively expand the extensional equivalence on 
  -- arbitrary functions. This is problematic when I want to prove that 𝐒𝐞𝐭 
  -- admits exponentials, in which case I need to show that the exponential
  -- object (Zʸ, λg) is unique, where λg : X → Y → Z. So I receive a goal of:
  --   λg x ≡ (λ y → g (x , y)) 
  -- where λg x : Y → Z, but what I would really like is the goal:
  --   λg x y ≡ g (x , y)
  -- To demonstrate:
  open Category (𝐒𝐞𝐭 lzero)
  problem : ∀ {A B C : Obj} (f g : A ⇒ (B ⇒ C)) → 
            (f ≈ g) ≡ (∀ (x : A) → f x ≡ g x)
  problem f g = refl 

------------------------------------------------------------------------------
-- As an example, List is an Endofunctor on 𝐒𝐞𝐭

ListFunctor : Endofunctor (𝐒𝐞𝐭 ℓ)
ListFunctor = record 
  { F₀ = List 
  ; fmap = map 
  ; F-id = λ xs → map-id xs 
  ; F-∘ = λ f g xs → map-∘ xs
  ; F-cong = map-cong  }

-- ------------------------------------------------------------------------------
-- initial and terminal objects in 𝐒𝐞𝐭

-- ⊤ is a terminal object in Set.
SetTerminal : ∀ {o} → isTerminal (𝐒𝐞𝐭 o) ⊤ 
SetTerminal = term (λ _ _ → tt) (λ f a → refl)

-- ⊥ is an initial object in Set.
SetInitial : ∀ {o} → isInitial (𝐒𝐞𝐭 o) ⊥ 
SetInitial = init (λ _ ()) λ { _ () }

-------------------------------------------------------------------------
-- _*_ forms products on 𝐒𝐞𝐭

open hasProduct  
open AdmitsProducts 

𝐒𝐞𝐭Products : ∀ ℓ → AdmitsProducts (𝐒𝐞𝐭 ℓ) 
𝐒𝐞𝐭Products _ ._×_ = _*_
𝐒𝐞𝐭Products _ .`π₁ = fst
𝐒𝐞𝐭Products _ .`π₂ = snd
𝐒𝐞𝐭Products _ .⟨_,_⟩ f g x = (f x , g x)
𝐒𝐞𝐭Products _ .project₁ _ = refl 
𝐒𝐞𝐭Products _ .project₂ _ = refl 
𝐒𝐞𝐭Products ℓ  .unique eq₁ eq₂ x = 
  cong₂ _,_ (sym (eq₁ x)) (sym (eq₂ x)) 

-------------------------------------------------------------------------
-- _→_ forms exponentials on 𝐒𝐞𝐭

module _ ℓ where 
  open AdmitsProducts (𝐒𝐞𝐭Products ℓ) 
  open hasExponential
  open AdmitsExponentials
  open import Categories.Prelude.Equality.Extensionality.Propositional
  
  𝐒𝐞𝐭Exponentials : AdmitsExponentials (𝐒𝐞𝐭 ℓ) (𝐒𝐞𝐭Products ℓ)
  𝐒𝐞𝐭Exponentials .exponentials Y Z .Zʸ = Y → Z 
  𝐒𝐞𝐭Exponentials .exponentials Y Z .`eval (f , y) = f y
  𝐒𝐞𝐭Exponentials .exponentials Y Z .`λ[_]  f x y = f (x , y)
  𝐒𝐞𝐭Exponentials .exponentials Y Z .`transpose g (x , y) = refl
  -- Begrudgingly need extensionality, here. See note above.
  𝐒𝐞𝐭Exponentials .exponentials Y Z .`unique g λg λg-exponential x = 
    extensionality (λ y → λg-exponential (x , y)) 