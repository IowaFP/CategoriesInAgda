module Categories.Constructions.CWF where 

open import Data.Product.Properties using (,-injectiveʳ ; ,-injectiveˡ ; Σ-≡,≡→≡)

open import Categories.Prelude
open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation
open import Categories.Constructions.Initial
open import Categories.Instances.Set

open import Categories.Prelude.Equality.Heterogeneous
open HeterogeneousEquality

-- ------------------------------------------------------------------------------
-- Categories with families (and their use for modeling dependent type theory),
-- á la:
--   - Towards Formalizing Categorical Models of Type Theory in Type Theory.
--     Buisse and Dybjer, 2007.
--     - https://www.cse.chalmers.se/~peterd/papers/Bremen2007.pdf
--   - Internal Type Theory. Peter Dybjer. 1991
--     - https://www.cse.chalmers.se/~peterd/papers/InternalTT.pdf
--   - Syntax and Semantics of Dependent Types. Martin Hoffmann. 1997?
--     - https://www.cs.uoregon.edu/research/summerschool/summer14/rwh_notes/ssdt.pdf
--   - The groupoid interpretation of type theory. Martin Hofmann and Thomas Streicher. 1996
--     - https://ncatlab.org/nlab/files/HofmannStreicherGroupoidInterpretation.pdf
-- ------------------------------------------------------------------------------
-- Can't be bothered with proving certain extensional equivalence properties of
-- families of sets. It seems I really do need functional extensionality, 
-- which means we lose computational properties, anyway.

postulate sorry : ∀ {ℓ} {A : Set ℓ} → A 

-- ------------------------------------------------------------------------------
-- The category of families of sets (type-theoretically)

module _ where 

  open Category 

  record Fam ℓ₁ ℓ₂ : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where 
    constructor _,_
    field
      index    : Set ℓ₁ 
      elements : index → Set ℓ₂

  open Fam 

  record FamMorphism (F G : Fam ℓ₁ ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where 
    constructor _,_ 
    field 
        indexMap : F .index → G .index
        elementMap : ∀ (x : F .index)  → F .elements x → G .elements (indexMap x)
  
  open FamMorphism
  -- -- The category of families of (small) sets
  -- TODO clean all of this up
  𝐅𝐚𝐦 : ∀ (ℓ₁ ℓ₂ : Level) → Category (lsuc (ℓ₁ ⊔ ℓ₂)) (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂) 
  𝐅𝐚𝐦 ℓ₁ ℓ₂ .Obj = Fam ℓ₁ ℓ₂
  𝐅𝐚𝐦 ℓ₁ ℓ₂ ._⇒_ =  FamMorphism
  𝐅𝐚𝐦 ℓ₁ ℓ₂ ._∘_ (i₁ , g₁) (i₂ , g₂) = i₁ ○ i₂ , λ x a → g₁ (i₂ x) (g₂ x a)
  𝐅𝐚𝐦 ℓ₁ ℓ₂ .Id = id , (λ _ → id)
  -- This definition of equality is very difficult to work with.
  -- N.b. Agda errors are from --cumulativity flag
  𝐅𝐚𝐦 ℓ₁ ℓ₂ ._≈_  {A = A} {B} (i₁ , g₁) (i₂ , g₂) =  
    ∀ (x : A .index) → (i₁ x ≡ i₂ x) * (∀ (y : A .Fam.elements x) → g₁ x y ≅ g₂ x y)
  𝐅𝐚𝐦 ℓ₁ ℓ₂ .eqv  .IsEquivalence.refl x = refl , λ _ → refl 
  𝐅𝐚𝐦 ℓ₁ ℓ₂ .eqv  .IsEquivalence.sym x≈y i = cross sym (λ a y → sym-≅ (a y)) (x≈y i) 
  -- There must be a cleverer way of writing this
  𝐅𝐚𝐦 ℓ₁ ℓ₂ .eqv  .IsEquivalence.trans x≈y y≈z i = (cross (trans (x≈y i .fst)) (λ a y → trans-≅ (x≈y i .snd y) (a y)) (y≈z i)) 
  𝐅𝐚𝐦 ℓ₁ ℓ₂ .cong-∘ {B = B₁} {C = C} {f = i₁ , f} {i₂ , h} {i₃ , g} {i₄ , j} eq₁ eq₂ x = sorry 
    -- cong-both (λ y → eq₁ y .fst) (eq₂ x .fst) , λ y → 
    -- cong-app-≅ {x = g x y} {j x y} 
    --   (subst (λ X → (λ _ → C .B (i₁ (i₃ x))) ≅ (λ _ → C .B X)) (cong-both (λ y → eq₁ y .fst) (eq₂ x .fst)) {! refl     !}) 
    --   (f (i₃ x)) 
    --   (h (i₄ x)) 
    --   (cong-app-≅ 
    --     {! subst (λ X → (λ z → B₁ .B z → C .B (i₁ z)) ≅ (λ z → B₁ .B z → C .B (i₂ z)))   !} f h 
    --     {!   !} (≡-to-≅ (eq₂ x .fst))) (eq₂ x .snd y) 
  𝐅𝐚𝐦 ℓ₁ ℓ₂ .idᵣ x = refl , λ _ → refl
  𝐅𝐚𝐦 ℓ₁ ℓ₂ .idₗ x = refl , λ _ → refl
  𝐅𝐚𝐦 ℓ₁ ℓ₂ .assₗ x = refl , λ _ → refl


{- ------------------------------------------------------------------------------
Categories with families---a primer

CWFs are a semantic analogue to Martin Lof's "Substitution Calculus".
Our base category Con is a category of *contexts*, in which arrows are substitutions.
Let Γ and Δ = x₁ : τ₁ , ... , xₙ : τₙ be two valid contexts. Then if f = (M₁ , ... , Mₙ) 
is a sequence of terms, we write
  Γ ⊢ σ ⇒ Δ 
and say that σ is a context morphism from Γ to Δ if the following n judgments hold:
  - Γ ⊢ M₁ : τ₁
  - Γ ⊢ M₂ : τ₂[M₁ / x₁]
  - ... 
  - Γ ⊢ Mₙ : τₙ[M­₁ / x₁][M₂ / x₂]...[Mₙ₋₁ / xₙ₋₁]
In other words, Δ is the context housing variables and Γ is the context
in which each term M₁ ... Mₙ types. We can confirm now that the empty context ⟨⟩
is terminal: for any Γ, we have Γ ⊢ () ⇒ ⟨⟩ because, trivially, each (M₁ : τ₁) in
() types under Γ.

In an intrinsic formalization, we cannot write substitution recursively. We would
be tempted to define a substitution (i.e., a context morphism) as the type:
  Substitution : (Γ Δ : Context) → Set ℓ 
  Substitution Γ Δ = ∀ {τ : Type Δ} → Var Δ τ → Term Γ ? 
and define term substitution with the type:
  subst : ∀ {Γ Δ} → Term Δ τ → Substitution Γ Δ → Term Γ ?
but the cart gets before the horse: the term we are returning is indexed by a type
that must be substituted! Hence formalizations of CWFs typically represent 
substitutions inductively, i.e., 
  data Substitution : (Γ Δ : Context) → Set where 
      ⋄ : Substitution Γ ⟨⟩ 
      _,_ : Substitution Γ Δ → Type 
      _,_ : Substitution Γ Δ → Term Γ τ → Substitution Γ (Δ , τ)
      ... 
Note that under this definition, substitution is contravariant--hence a CWF 
has a contravariant functor Ty : Conᵒᵖ → Fam. We define type and term substitution (resp.)
below.
  _[_] : ∀ {Γ Δ : Obj} (τ : Type Δ) (σ : Γ ⇒ Δ) → Type Γ 
  τ [ σ ] = fmap σ .indexMap τ
  _⁅_⁆ : ∀ {Γ Δ : Obj} {τ : Type Δ} 
             (M : Term Δ τ) (σ : Γ ⇒ Δ) → Term Γ (τ [ σ ])
Intuitively, this is because Δ tells us the types of the *free* variables in a given term, 
and Γ tells us the context in which they type. Substitution is total, and so *all* of the
variables in Δ disappear (or are placed in Γ if we substitute a variable for a variable.)
-}

record CWF {ℓ} (Con : Category o a e) : Set (lsuc (lsuc o) ⊔ e ⊔ a ⊔ lsuc (lsuc ℓ)) where 
  open Category Con 
  open Fam
  open FamMorphism

  Conᵒᵖ = op 

  field 
    Ty : Functor Conᵒᵖ (𝐅𝐚𝐦 o ℓ)
    ⟨⟩ : Obj 
    ⟨⟩-terminal : isTerminal Con ⟨⟩ 
  open Functor Ty 

  Type : Obj → Set o 
  Type Γ = F₀ Γ .index

  Term : (Γ : Obj) → Type Γ → Set ℓ 
  Term Γ τ = F₀ Γ .elements τ

  -- Type substitution
  infixr 5 _[_] 
  _[_] : ∀ {Γ Δ : Obj} (τ : Type Δ) (σ : Γ ⇒ Δ) → Type Γ 
  τ [ σ ] = fmap σ .indexMap τ

  -- Term substitution
  infixr 5 _⁅_⁆
  _⁅_⁆ : ∀ {Γ Δ : Obj} {τ : Type Δ} 
             (M : Term Δ τ) (σ : Γ ⇒ Δ) → Term Γ (τ [ σ ])
  _⁅_⁆ M σ = fmap σ .elementMap _ M 

  infixr 6 _▷_             
  field 
    -- Context comprehension/extension
    _▷_ : ∀ (Γ : Obj) (τ : Type Γ) → Obj 
    -- The first and second projection---
    -- Think of p as the substitution extended with M
    -- and q as the term pointing to the zero'th De Bruijn index.
    p : ∀ (Γ : Obj) (τ : Type Γ) → Γ ▷ τ ⇒ Γ 
    q : ∀ (Γ : Obj) (τ : Type Γ) → 
               Term (Γ ▷ τ) (τ [ (p Γ τ) ]) 
    -- Extension of a substitution by a term
    ⟨_,_∋_⟩ : ∀ {Δ Γ : Obj} (σ : Δ ⇒ Γ) (τ : Type Γ)
               (M : Term Δ (τ [ σ ])) → 
               Δ ⇒ Γ ▷ τ

  -- Computational rules for context comprehension:
  -- - Extending σ with M then projecting out σ yields σ.
  -- - Substitution of q by a substitution extended with M
  --   yields M.
  PLaw : ∀ (Δ Γ : Obj) (σ : Δ ⇒ Γ) 
                (τ : Type Γ) (M : Term Δ (τ [ σ ]))
                (θ : Δ ⇒ Γ ▷ τ) → 
                Set e
  PLaw Δ Γ σ τ M θ = (p Γ τ) ∘ θ ≈ σ
  QLaw : ∀ (Δ Γ : Obj) (σ : Δ ⇒ Γ) 
                (τ : Type Γ) (M : Term Δ (τ [ σ ])) → 
                (θ : Δ ⇒ Γ ▷ τ) → 
                Set ℓ  
  QLaw Δ Γ σ τ M θ = (q Γ τ) ⁅ θ ⁆ ≅ M

  field 
    p-law : ∀ (Δ Γ : Obj) (σ : Δ ⇒ Γ) 
              (τ : Type Γ) (M : Term Δ (τ [ σ ])) → 
              PLaw Δ Γ σ τ M ⟨ σ , τ ∋ M ⟩ 
    q-law : ∀ (Δ Γ : Obj) (σ : Δ ⇒ Γ) 
              (τ : Type Γ) (M : Term Δ (τ [ σ ])) → 
              QLaw Δ Γ σ τ M ⟨ σ , τ ∋ M ⟩ 
    unique : ∀ (Δ Γ : Obj) (σ : Δ ⇒ Γ) 
               (τ : Type Γ) (M : Term Δ (τ [ σ ]))
               (θ : Δ ⇒ Γ ▷ τ) 
               (P : PLaw Δ Γ σ τ M θ)
               (Q : QLaw Δ Γ σ τ M θ) → 
               ⟨ σ , τ ∋ M ⟩ ≈ θ 

-- ------------------------------------------------------------------------------
-- A trivial CWF model

module _ where 
  open Category (𝐒𝐞𝐭 lzero)
  open CWF
  open Fam ; open FamMorphism 
  open Functor 

  SetCWF : CWF {ℓ = lzero} (𝐒𝐞𝐭 lzero) 
  -- We let Ty(Γ) = the set of Γ-indexed sets
  SetCWF .Ty .F₀ Γ .index = Γ → Set 
  -- Let Term Γ A = { A(x) ∣ x ∈ Γ }
  SetCWF .Ty .F₀ Γ .elements A = ∀ (x : Γ) → A x
  SetCWF .Ty .fmap σ = (λ Ty → Ty ○ σ) , (λ Ty Tm → Tm ○ σ)
  SetCWF .Ty .F-∘ = sorry
  SetCWF .Ty .F-id = λ Ty → refl , λ _ → refl
  SetCWF .Ty .F-cong = sorry
  SetCWF .⟨⟩ = ⊤
  SetCWF .⟨⟩-terminal = SetTerminal
  SetCWF ._▷_ Γ A = Σ[ x ∈ Γ ] (A x)
  -- Here we confirm that p and q really are projections.
  SetCWF .p Con Ty (Γ , τ) = Γ
  SetCWF .q Γ τ (σ , τ[σ]) = τ[σ]
  SetCWF .⟨_,_∋_⟩ σ τ M δ = (σ δ) , (M δ)
  SetCWF .p-law Δ Γ σ τ M x = refl
  SetCWF .q-law Δ Γ σ τ M = refl
  -- Need extensionality, again, and I'm not sure a way around it.
  SetCWF .unique Δ Γ σ τ M θ plaw qlaw x with 
        θ x   | plaw x | cong-app-≅ {x = x} {x} {! plaw x  !} (snd ○ θ) M qlaw refl
  ... | δ , t | refl   | refl = refl 


-- --------------------------------------------------------------------------} 

-- ---------------------------------------------------------------------------
-- Morphisms between CWFs (so that we may form a category of CWFs)

module _ {𝒞 𝒟 : Category o a e} where 
  open Category ; open Fam ; open FamMorphism ; open CWF 
  open Isomorphism 𝒟 ; open Functor 

  private 
    module C = Category 𝒞 ; module D = Category 𝒟
  
  record CWFMorphism {ℓ} (𝒜 : CWF {ℓ = ℓ} 𝒞) (ℬ : CWF {ℓ = ℓ} 𝒟) :  Set {!   !} where
    private 
      module A = CWF 𝒜 ; module B = CWF ℬ
    Ty₁ : Functor C.op (𝐅𝐚𝐦 o ℓ)
    Ty₁ = A.Ty 

    Ty₂ : Functor D.op (𝐅𝐚𝐦 o ℓ)
    Ty₂ = B.Ty 

    field 
      F : Functor 𝒞 𝒟
      η : NaturalTransformation Ty₁ (Ty₂ ∘F (opF F))
      preserves-terminal : F .F₀ (A.⟨⟩) ≡ B.⟨⟩ 
      preserves-comprehension : ∀ (Γ : C.Obj) (τ : A.Type Γ) → {!   !} -- F .F₀ (Γ A.▷ τ) ≃ ((F .F₀ Γ) B.▷ (F .F₀ τ))


-- ------------------------------------------------------------------------------
-- Pullbacks + terminal object ⇒ all finite limits

-- ------------------------------------------------------------------------------
-- Initiality should yield us the syntax of (base) MLTT
