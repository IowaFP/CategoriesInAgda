module Categories.TypeTheory.Monad where 

open import Prelude hiding (_>>=_)
open import Categories.Prelude 

open PropositionalEquality
--------------------------------------------------------------------------------
-- Isomorphism

record Iso {ℓ₁} {ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) : Set (lsuc ℓ₁ ⊔ ℓ₂) where 
  constructor iso  
  field
    g : B → A 
    rinv : f ○ g ~ id
    linv : g ○ f ~ id

--------------------------------------------------------------------------------
-- Functors

record Functor {ℓ} (F₀ : Set ℓ → Set ℓ) : Set (lsuc ℓ) where
  constructor Func
  infixl 5 _$_ 

  field 
    _$_ : ∀ {A B : Set ℓ}  → (A → B) → F₀ A → F₀ B 
  fmap = _$_ 
  _₀ = F₀ 
  ₀ = F₀ 
  _₁ = fmap 
  ₁ = fmap 


_⊗_ : ∀ {F G : Set ℓ → Set ℓ} → Functor F → Functor G → Functor (F ○ G) 
(Func fmap) ⊗ (Func gmap) = Func (λ f → fmap (gmap f))

record FunctorLaws {ℓ₁} {F₀ : Set ℓ₁ → Set ℓ₁} (F₁ : Functor F₀) : Set (lsuc ℓ₁) where 
    open Functor F₁ 
    field 
      FunctorId : fmap {A = A} id ~ id 
      FunctorComp : ∀ {A B C D : Set ℓ₁} → 
                      (g : B → C) → (f : A → B) → 
                      fmap (g ○ f) ~ fmap g ○ fmap f                      

IdF : ∀ {ℓ} → Functor {ℓ} (λ X → X) 
IdF .Functor._$_ f = f 

open FunctorLaws 

IdFLaws : ∀ {ℓ} → FunctorLaws {ℓ} IdF 
IdFLaws .FunctorId x = refl 
IdFLaws .FunctorComp _ _ _ = refl 

--------------------------------------------------------------------------------
-- Bifunctors

record Bifunctor {ℓ₁} {ℓ₂} (F : Set ℓ₁ → Set ℓ₁ → Set ℓ₂) : Set (lsuc ℓ₁ ⊔ ℓ₂) where
  constructor Bifunc 
  infixl 5 _$$_ 

  field 
    bmap : ∀ {A B C D : Set ℓ₁}  → (A → B) → (C → D) → F A C → F B D 
  _$$_ : ∀ {A B C D : Set ℓ₁}  → (A → B) × (C → D) → F A C → F B D 
  (f , g) $$ x = bmap f g x 

record BifunctorLaws {ℓ₁} {ℓ₂} {F₀ : Set ℓ₁ → Set ℓ₁ → Set ℓ₂} (F₁ : Bifunctor F₀) : Set (lsuc ℓ₁ ⊔ ℓ₂) where 
    open Bifunctor F₁ 
    field 
      BifunctorId : bmap {A = A} {C = C} id id ~ id 
      BifunctorComp : ∀ {A₀ B₀ C₀ D₀ A₁ B₁ C₁ D₁ : Set ℓ₁} → 
                      (g₀ : B₀ → C₀) → (f₀ : A₀ → B₀) → 
                      (g₁ : B₁ → C₁) → (f₁ : A₁ → B₁) → 
                      bmap (g₀ ○ f₀) (g₁ ○ f₁) ~ bmap g₀ g₁ ○ bmap f₀ f₁

BFPrj₁ : ∀ {ℓ₁} {F : Set ℓ₁ → Set ℓ₁ → Set ℓ₁} → Bifunctor F → (A : Set ℓ₁) → Functor (λ X → F X A) 
BFPrj₁ (Bifunc bmap) I .Functor._$_ f = bmap f id 

BFPrj₂ : ∀ {ℓ₁} {F : Set ℓ₁ → Set ℓ₁ → Set ℓ₁} → Bifunctor F → (A : Set ℓ₁) → Functor (F A) 
BFPrj₂ (Bifunc bmap) _ .Functor._$_ f = bmap id f

-- Functor composition forms a Bifunctor 

ComposeBifunctor : ∀ {ℓ} → Bifunctor {ℓ} {! _⊗_  !}
ComposeBifunctor .Bifunctor.bmap f g = {!   !} 

--------------------------------------------------------------------------------
-- Natural Transformations

record Nat {ℓ₁} {F₀ G₀ : Set ℓ₁ → Set ℓ₁} 
           (F : Functor F₀) (G : Functor G₀)  : Set (lsuc ℓ₁) where 
    constructor nat
    field 
      η : ∀ {A : Set ℓ₁} → F₀ A → G₀ A  

record NatLaws {ℓ₁} {F₀ G₀ : Set ℓ₁ → Set ℓ₁} 
               {F : Functor F₀} {G : Functor G₀} 
               (nat : Nat F G) : Set (lsuc ℓ₁) where 
    instance 
        _ : Functor F₀ 
        _ = F 
        _ : Functor G₀ 
        _ = G 

    open Nat nat 
    open Functor {{...}}
    field 
        naturality : ∀ {A B : Set ℓ₁} → (f : A → B) → 
                      fmap f ○ η ~ η ○ fmap f

-- vertical composition
_∘V_ : ∀ {ℓ₁} {F₀ G₀ H₀ : Set ℓ₁ → Set ℓ₁} 
         {F : Functor F₀} {G : Functor G₀} {H : Functor H₀} → 
         Nat G H → Nat F G → Nat F H 
((nat η) ∘V (nat ε)) .Nat.η  = η ○ ε

-- horizontal composition
_∘H_ : ∀ {ℓ₁} {F₀ G₀ J₀ K₀ : Set ℓ₁ → Set ℓ₁} 
         {F : Functor F₀} {G : Functor G₀} {J : Functor J₀} {K : Functor K₀} → 
         Nat F G → Nat J K → Nat (F ⊗ J) (G ⊗ K) 
_∘H_ {F = Func fmap} {Func gmap} {Func jmap} {Func kmap} 
    (nat η) (nat ε) .Nat.η = gmap ε ○ η

idN : ∀ {ℓ} → Nat {ℓ} IdF IdF 
idN .Nat.η = id 

open NatLaws 

idNLaws : ∀ {ℓ} → NatLaws {ℓ} idN 
idNLaws .naturality _ _ = refl


                      
--------------------------------------------------------------------------------
-- Monoidal Categories

record Monoidal {ℓ} (_⊗_ : Set ℓ → Set ℓ → Set ℓ) (BF : Bifunctor _⊗_) : Set (lsuc ℓ) where 
    open Nat 
    open Bifunctor BF 
    infixr 5 _⊗₁_
    _⊗₁_ = bmap 

    field 
        I : Set ℓ 
        α : ∀ {A B C : Set ℓ} → (A ⊗ B) ⊗ C → A ⊗ (B ⊗ C)
        αIso : ∀ {A B C : Set ℓ} → Iso {A = (A ⊗ B) ⊗ C } {B = A ⊗ (B ⊗ C)} α

        leftUnit : let I⊗— = BFPrj₂ BF I in Nat I⊗— IdF 
        leftUnit-iso : ∀ {A : Set ℓ} → Iso {A = I ⊗ A} {B = A} ((leftUnit .η) {A})
        rightUnit : let —⊗I = BFPrj₁ BF I in Nat —⊗I IdF 
        rightUnit-iso : ∀ {A : Set ℓ} → Iso {A = A ⊗ I} {B = A} ((rightUnit .η) {A})        

    λₘ = leftUnit .η 
    ρₘ = rightUnit .η

record Monoid {ℓ} (_⊗_ : Set ℓ → Set ℓ → Set ℓ) (BF : Bifunctor _⊗_) (mon : Monoidal _⊗_ BF) : Set (lsuc ℓ) where 
    open Monoidal mon 
    open Bifunctor BF 

    field 
      M : Set ℓ 
      μ : M ⊗ M → M 
      η : I → M

      pentagon : μ ○ (μ ⊗₁ id) ~ μ ○ (id ⊗₁ μ) ○ α
      unitor-λ : μ ○ (η ⊗₁ id) ~ λₘ 
      unitor-ρ : μ ○ (id ⊗₁ η) ~ ρₘ 

--------------------------------------------------------------------------------
-- Monads & the monad laws 

record Monad {ℓ₁} {M₀ : Set ℓ₁ → Set ℓ₁} (M : Functor M₀) : Set (lsuc ℓ₁ ⊔ ℓ₂) where 
  open Nat 
  open Functor M 

  field 
    return-nat : Nat IdF M 
    bind : ∀ {A B : Set ℓ₁} → M₀ A → (A → M₀ B) → M₀ B 

  return = return-nat .η 

  infixl 4 _>>=_
  _>>=_ = bind 

  μ : M₀ (M₀ A) → M₀ A 
  μ {A = A} = _>>= id  

record MonadLaws {ℓ} {M₀ : Set ℓ → Set ℓ} {Mf : Functor M₀} (M : Monad {ℓ} Mf) : Set (lsuc ℓ)  where 
    open Monad M 
    open Functor Mf 

--------------------------------------------------------------------------------
-- A monad is just a monoid in a category of Endofunctors!


