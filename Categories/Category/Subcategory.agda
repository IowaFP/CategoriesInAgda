{-# OPTIONS --without-K #-}
module Categories.Category.Subcategory where

open import Categories.Prelude
open import Categories.Category
open import Categories.Functor 
open import Categories.NaturalTransformation


--------------------------------------------------------------------------------
{- 
A subcategory 𝒞 of category 𝒟 is defined pretty loosely as a 
subcollection of objects and morphisms in 𝒟 such that
- if f : A → B is in 𝒞, then A and B are objects in 𝒞,
- if f : A → B and G : B → C are in 𝒞, then (g ○ f) : A → C is in 𝒞, and
- if A is an object in 𝒞 then the identity morphism Id : A → A is in 𝒞.
These rules simply enforce that 𝒞 be a category. 
We will first formalize subcategories along these lines,
choosing to instead describe a subcategory by the objects and morphisms it chooses.
What follows is more or less ripped off verbatim from The Agda categories library.
https://github.com/agda/agda-categories/blob/2530add4640337202357934f01151b73ea8df362/src/Categories/Category/SubCategory.agda
They write:
  Here a SubCategory is defined via
    - an index set I
    - a mapping I → Obj (not necessarily injective)
    - a proof (as a unary relation) that for all a, b : I, all arrows U a ⇒ U b 
      belong to the SubCategory (note that this is 'backwards' from SubCategory 
      at https://ncatlab.org/nlab/show/subcategory which would be
      (∀ {x y : Obj} (f : x ⇒ y) → R f → ∃ (A × B) (λ (a , b) → U a × U b))
      and that would be awkward to work with.
    - a proof that all objects pointed to by I have identity arrows that belong
    - a proof that composable arrows in the SubCategory are closed under composition
-} 
--------------------------------------------------------------------------------
-- An inclusion specifies the objects and arrows of 𝒟 to include in 𝒞.
-- The index U : I → Obj specifies which objects in 𝒟 to include,
-- and the relation R : U A ⇒ U B → Set specifies which arrows in 𝒟
-- to include.

module _ (𝒟 : Category o a e) where 
  open Category 𝒟
  open Isomorphism 𝒟

  record Inclusion (I : Set ℓ₁) {ℓ₂} : Set (o ⊔ a ⊔ e ⊔ ℓ₁ ⊔ lsuc ℓ₂) where
    constructor inclusion 
    field 
      U  : I → Obj 
      R : {A B : I} → U A ⇒ U B → Set ℓ₂ 
      R-id : ∀ {A : I} → R (Id {U A})
      _∘R_ : {A B C : I} {f : U B ⇒ U C} {g : U A ⇒ U B} → R f → R g → R (f ∘ g)
      -- In contrast with the Agda Categories library, I really *would*
      -- like to force that U be injective on objects.
      U-injective : ∀ {A B : I} → (p : U A ≃ U B) → R (p .morph) * R (p .iso .∼)

--------------------------------------------------------------------------------
-- From an Inclusion we can build a (sub)category

  open Inclusion 

  Subcategory : (I : Set ℓ₁) → Inclusion I {ℓ₂} → Category _ _ _ 
  Subcategory I _ .Category.Obj = I
  Subcategory I (inclusion U R _ _ _) .Category._⇒_ A B = Σ[ f ∈ (U A ⇒ U B) ] (R f)
  Subcategory I (inclusion _ _ _ _∘R_ _) .Category._∘_ (f , Rf) (g , Rg) = (f ∘ g) , (Rf ∘R Rg)
  Subcategory I (inclusion _ _ R-id _ _) .Category.Id = Id , R-id
  Subcategory I _ .Category._≈_ (f , _) (g , _) = f ≈ g 
  Subcategory I _ .Category.eqv .IsEquivalence.refl = refl-≈
  Subcategory I _ .Category.eqv .IsEquivalence.sym = sym-≈ 
  Subcategory I _ .Category.eqv .IsEquivalence.trans = trans-≈
  Subcategory I _ .Category.idᵣ = idᵣ
  Subcategory I _ .Category.idₗ = idₗ
  Subcategory I _ .Category.assₗ = assₗ
  Subcategory I _ .Category._⋆_ = _⋆_ 

  -- A full subcategory has an inclusion functor that is full. Consequently, it is 
  -- sufficient to specify just which objects occur. (As we know that
  -- the hom-set in 𝒞 between any two objects is precisely the hom-set in 𝒟.)
  FullSubcategory : (I : Set ℓ₁) (U : I → Obj) → Category _ _ _ 
  FullSubcategory I U .Category.Obj = I
  FullSubcategory I U .Category._⇒_ A B = U A ⇒ U B
  FullSubcategory I U .Category._∘_ = _∘_
  FullSubcategory I U .Category.Id = Id
  FullSubcategory I U .Category._≈_ = _≈_
  FullSubcategory I U .Category.eqv = eqv
  FullSubcategory I U .Category.idᵣ = idᵣ
  FullSubcategory I U .Category.idₗ = idₗ
  FullSubcategory I U .Category.assₗ = assₗ
  FullSubcategory I U .Category._⋆_ = _⋆_ 

--------------------------------------------------------------------------------
-- We also specify a subcategory as a relation on categories.

record isSubcategory (𝒞 : Category o₁ a₁ e₁) (𝒟 : Category o₂ a₂ e₂) : 
       Set ((lsuc o₁) ⊔ a₁ ⊔ e₁ ⊔ (lsuc o₂) ⊔ a₂ ⊔ e₂) where 
  field 
    ι : 𝒞 ⇛ 𝒟 
    faithful : Faithful ι 
    injective : EssentiallyInjective ι 

open isSubcategory public 

infixr 7 _⊆_
_⊆_ = isSubcategory

record isFullSubcategory (𝒞 : Category o₁ a₁ e₁) (𝒟 : Category o₂ a₂ e₂) : 
       Set ((lsuc o₁) ⊔ a₁ ⊔ e₁ ⊔ (lsuc o₂) ⊔ a₂ ⊔ e₂) where 
  field 
    ι : 𝒞 ⇛ 𝒟 
    faithful : Faithful ι 
    injective : EssentiallyInjective ι 
    full : Full ι 

infixr 7 _⊑_
_⊑_ = isFullSubcategory


-- --------------------------------------------------------------------------------
-- We prove that the (sub)categories we've built cohere with the definition
-- via functors.

module _ (𝒟 : Category o a e) where 
  open Category 𝒟
  open Functor 
  open Inclusion 
  open Isomorphism 𝒟 
  open isFullSubcategory

  -- Every subcategory definition yields an inclusion functor
  ι-Sub : ∀ {ℓ₂} {I : Set ℓ₁} → (ι : Inclusion 𝒟 I {ℓ₂}) → 
                    (Subcategory 𝒟 I ι) ⇛ 𝒟
  ι-Sub inc .F₀ = inc .U
  ι-Sub inc .fmap = fst 
  ι-Sub inc .F-id = refl-≈
  ι-Sub inc .F-∘ f g = refl-≈
  ι-Sub inc .F-cong eq = eq   

  -- This inclusion functor is faithful & injective on objects (up to
  -- isomorphism).
  Subcategory⇒isSubcategory : ∀ {I : Set ℓ₁} → (ι : Inclusion 𝒟 I {ℓ₂}) → 
                                (Subcategory 𝒟 I ι) ⊆ 𝒟
  Subcategory⇒isSubcategory ι .ι = ι-Sub ι
  Subcategory⇒isSubcategory ι .faithful f g eq = eq 
  Subcategory⇒isSubcategory (inclusion U₁ R₁ R-id₁ _∘R_ U-injective) 
    .injective iso@(f , f⁻¹ , linv , rinv) = 
    -- TODO: don't know why Agda is erroring when I use _,_ instead of the qualified name Isomorphism.,
      (f , U-injective iso .fst) Isomorphism., 
      ((f⁻¹ , U-injective iso .snd) , linv , rinv) 

  -- Every full subcategory definition yields a full inclusion functor
  ι-Full : ∀ {I : Set ℓ₁} → (U : I → Obj) → 
                     (FullSubcategory 𝒟 I U) ⇛ 𝒟
  ι-Full U .F₀ = U
  ι-Full U .fmap = id 
  ι-Full U .F-id = refl-≈
  ι-Full U .F-∘ f g = refl-≈
  ι-Full U .F-cong eq = eq   

  FullSubcategory⇒isFullSubcategory : ∀ {I : Set ℓ₁} → (U : I → Obj) → 
                                        (FullSubcategory 𝒟 I U) ⊑ 𝒟
  FullSubcategory⇒isFullSubcategory U .ι = ι-Full U
  FullSubcategory⇒isFullSubcategory U .faithful f g eq = eq 
  FullSubcategory⇒isFullSubcategory U .injective (f , f⁻¹ , linv , rinv) = f Isomorphism., (f⁻¹ , linv , rinv)
  FullSubcategory⇒isFullSubcategory U .full g = g , refl-≈