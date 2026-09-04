```agda 
{-# OPTIONS --rewriting #-}
module Categories.TypeTheory.DTT.Syntax where 
``` 

# Imports 
We won't be doing much categorical nonsense, but we'll its Prelude nonetheless. We import rewriting in the case we choose to rewrite by some equalities later.

```agda  
open import Agda.Builtin.Equality.Rewrite 

open import Categories.Prelude hiding (_○_ ; id ; _·_ ; _⁻¹ ; _●_)
open PropositionalEquality
``` 

# Notation 

Permit me some HoTT notation. 

```agda 
-- HoTT names 
ap = cong 
_⁻¹ = sym 
_●_ = trans 

-- transports 
tr = subst 

-- syntactic sugar for transports (\tb2)
infixr 5 _▸_ 
_▸_ : ∀ {A : Set ℓ₁} {P : A → Set ℓ₂} {x y : A} → x ≡ y → P x → P y
p ▸ x = tr _ p x 

-- With explicit motive 
infixr 5 _⟨_⟩▸_
_⟨_⟩▸_ :  ∀ {A : Set ℓ₁} (P : A → Set ℓ₂) {x y : A} → x ≡ y → P x → P y
_⟨_⟩▸_ = tr
``` 


# Dependent Type Theory 

In ../STLC, we model/interpret the syntax of the STLC into *any* CCC. When we choose 𝐒𝐞𝐭 as our CCC, we recover the traditional set-theoretic semantics of the STLC. When ℂ is a category of contexts, then the choice of [ℂᵒᵖ, 𝐒𝐞𝐭], the category of presheaves on ℂ, recovers the *intrinsic syntax* of the STLC. This is analogous to *initial* syntax. 

Our next challenge is to produce the same framework but for *dependent type theory*. The construction notably involves an *explicit substitution calculus*, in which substitutions are first-class data types. This involves the internalization of a number of computational rules on substitutions. The means by which one deals with these computational rules without falling into Transport Hell is still an active area of research. 


## Extant work 

A few approaches and extant attempts:
- Disregarding the category theory, Danielsson gives an intrinsic formalization
  in Agda of Dependent Type Theory. This work is early, and predates many
  Agda features, or any *fancy* type theory features, such as QITs.
    - A formalisation of a dependently typed language as an inductive-recursive family. Danielsson, N.A.
      - https://www.cse.chalmers.se/~nad/publications/danielsson-types2006.pdf
- Buisse and Dybjer effectively beat me to the punch by encoding
  a categorical interpretation, with suitable definitions of categories in Agda:
  - Towards Formalizing Categorical Models of Type Theory in Type Theory. Alexandre Buisse and Peter Dybjer. 
    - https://www.cse.chalmers.se/~peterd/papers/Bremen2007.pdf
- These authors try to overcome transport hell with Cubical Agda.
  - Liang-Ting Chen, Fredrik Nordvall Forsberg, Tzu-Chun Tsai. Can We Formalize Type Theory Intrinsically without Any Compromise? A Case Study in Cubical Agda. CPP 2026. 
    - https://dl.acm.org/doi/pdf/10.1145/3779031.3779090   
- Altenkirch has done a lot of work on HITs and QIITs to model the syntax of DTT.
  - Quotient inductive-inductive types. Thorsten Altenkirch, Paolo Capriotti, Gabe Dijkstra, Nicolai Kraus, and Fredrik Nordvall Forsberg. 2018. 
    - https://arxiv.org/pdf/1612.02346   
  - Type theory in type theory using quotient inductive types. 
  Thorsten Altenkirch and Ambrus Kaposi. 2016.
  https://dl.acm.org/doi/10.1145/2837614.2837638
- Finally, much of the nuisances we "discover" in this development are
  described by Kaposi et al.
  - Shallow Embedding of Type Theory is Morally Correct. Ambrus Kaposi, Andras Kovacs, Nicolai Kraus.
    - https://arxiv.org/pdf/1907.07562

There are plenty other great formalizations I've omitted. This is all to say, this is well-trodden ground. Nevertheless, it will be fruitful to try on our own.

## The circularity problem

The syntax is made challenging, again, because of circularity. With System Fω, we have 
- kinds and kinding environments, which index
- types and typing environments, which index 
- terms. 

Here, there is no term-type-kind stratification, and terms appear in contexts. Notably, we cannot define substitution computationally. To illustrate, presume a set-up of contexts, types, terms, and variables:

```agda 
module Circularity where private 
  data Context : Set where 
  data Type (Δ : Context) : Set where 
  data Term : (Δ : Context) → Type Δ → Set where 
  data Var : (Δ : Context) → Type Δ  → Set where 

  private variable 
    Δ Γ : Context 
    τ υ : Type Δ 
```     

Now define substitutions as maps from variables to terms. Already, we see the problem: we are in the middle of defining what a substitution *is* and already need to ensure that τ : Type Γ is re-based to τ′ : Type Δ. That is, that is, we need to substitute τ!

```agda 
  Substitution : Context → Context → Set 
  Substitution Δ Γ = ∀ {τ} → Var Γ τ → Var Δ (subTy τ) 
    where postulate 
      subTy : Type Γ → Type Δ 
``` 

## Syntax 

We begin by declaring the mutually inductive definitions outright, as they  will require one another (contexts need types, types need contexts, terms need types, types need terms, and so forth).

Crucially, this definition is *inductive-inductive*: we will see below `Context` and `Type` are defined mutually, where `Type` is a *predicate* on `Context`. Further, constructors for e.g. `Var` will reference constructors for 
substitutions: the constructor `0`, the 0'th De Bruijn variable, must weaken 
its type τ.


```agda 
data Context            : Set
data Type (Δ : Context) : Set
data Term               : (Δ : Context) → Type Δ → Set
data Var                : (Δ : Context) → Type Δ  → Set
data Sub                : Context → Context → Set

-- Some constructors that appear 
infixl 5 _[_]ₜ
infixr 5 _▹_ 
infixr 3 _○_ 

private variable 
  Δ Γ Γ₁ Γ₂ Γ₃ Θ : Context 
  τ τ₁ τ₂ τ₃ υ υ₁ υ₂ υ₃ : Type Δ 
``` 

To avoid circularity, we represent an explicit **substitution calculus**, in which substitutions are data. Let's recall Hoffmann's description of *contexts* and *context* morphisms. We presume a category of contexts where the objects are of the form  Δ := x₁ : τ₁, ... , xₙ : τₙ. 

### Contexts 

Since we are working intrinsically, and with De Bruijn indices, it should be the case that each type in the context is well-formed. For example, in the context (∅ , A : 𝒰 , x : A → A) we see that each variable must be well-typed in the context that precedes it, hence:
- ∅ ⊢ A : 𝒰 
- ∅ , A : 𝒰 ⊢ x : A → A 
This leads to the following definition: when adding τ to a context, it must be well-typed in the context that precedes it. 

```agda 
data Context where 
  ∅     : Context
  _,_   : (Δ : Context) → Type Δ → Context
``` 

## Types 

Now define a minimal syntax of types: a universe 𝒰, dependent functions Π, and El, which interprets the universe code. Critically, we must also represent τ[ σ ]ₜ, the substitution of type τ by σ as first-class.


**remark**. I have never fully understood the point of `El` until now. In e.g. Agda, we don't write `∀ (A : 𝒰) (x : El(A)) → ...`, we just write `∀ (A : Set) (x : A) → ...`. The type `El` seems superfluous! But, aha! A subtlety: When we write `∀ (A : Set)`, we have (syntactically) that `A` is a variable, meaning a term! But when we quantify using Π, it must be over types! So `Π (x : A). M` is ill-typed. Specifically, we must have that `Γ, x : A ⊢ M : B`, but `A` is a term, not a type, hence we cannot throw it into our context.  In other words, `El` is necessary to convert the *term* `A` into the *type* that it represents.


```agda 
data Type Γ where 
  𝒰    : Type Γ
  Π     : (τ : Type Γ) → Type (Γ , τ) → Type Γ
  El    : Term Γ 𝒰 → Type Γ
  _[_]ₜ : Type Δ → Sub Γ Δ → Type Γ
``` 

## Substitutions 

In Hoffman's substitution category, the arrows f := M₁, ..., Mₙ, written Γ ⊢ f ⇒ Δ, are "context morphisms" from Γ to Δ if we have:
- Γ ⊢ M₁ : τ₁ 
- Γ ⊢ M₂ : τ₂[M₁/x₁]
- ... 
- Γ ⊢ Mₙ : τₙ[M₁/x₁][M₂/x₂]...[M_{n - 1}/x_{n - 1}]. 

Standard presentations of Substitutions-as-objects typically involves:
- the empty substitution ε (a terminal object),
- substitution composition `_○_`, 
- substitution extension `_▹_`, and 
- the identity substitution Id.

It seems the literature is still evolving on precisely the right
constructors for substitution. Moreover, we would like something
that most closely mirrors the *categorical construction*. Crucially,
we know that the definition of variables requires weakening; I will
follow [Altenkirch](Categories/TypeTheory/Notes/Altenkirch.agda), as well
as Chen et al in introducing substitution projections:
- π₁ : Sub Γ (Δ , τ) → Sub Γ Δ 
- π₂ : (σ : Sub Γ (Δ , τ)) → Term Γ (τ [ π₀ σ ]ₜ)
I frankly haven't quite unpacked what this all means.


```agda 
data Sub where 
  ε   : Sub Γ ∅
  _○_ : Sub Δ Θ → Sub Γ Δ → Sub Γ Θ
  _▹_ : (σ : Sub Γ Δ) → Term Γ (τ [ σ ]ₜ) → Sub Γ (Δ , τ)
  id   : Sub Γ Γ 
  π₁ : Sub Γ (Δ , τ) → Sub Γ Δ
``` 

Define weakening as a special case of the projection π₁:

```agda 
wk : Sub (Γ , τ) Γ
wk = π₁ id 
``` 

which permits the definition of non-dependent Π types, also called arrows: 

```agda 
_`→_ : Type Γ → Type Γ → Type Γ
τ `→ υ = Π τ (υ [ wk ]ₜ)
``` 

The sticky bits are that there are a number of equalities on substitutions--- e.g., that (M[ σ₁ ]) [ σ₂ ] ≡ M[ σ₁ ○ σ₂ ]. This is a leading reason of the use 
of **quotient inductive inductive types**, which are realized (cubically) as 
native HITs by Chen et al. 

**Remark.** To make matters worse, these equalities will necessarily need postulated. Take, for example, associativity of substitution:

```agda 
module Needed where 

  ass : ∀ {Ξ} → (σ₁ : Sub Θ Ξ) (σ₂ : Sub Δ Θ) (σ₃ : Sub Γ Δ) → 
        ((σ₁ ○ σ₂) ○ σ₃) ≡ (σ₁ ○ (σ₂ ○ σ₃))
  ass σ₁ σ₂ σ₃ = sorry 
``` 

or, simpler: substitution by the identity. What is there to do?
Nothing. In fact, it can't possibly hold! Constructors are disjoint!

```agda 
  sub-id : ¬ (τ [ id ]ₜ ≡ τ)
  sub-id {τ = τ} ()
``` 

We might be tempted to assert...

```agda 
postulate 
  ass : ∀ {Ξ} → (σ₁ : Sub Θ Ξ) (σ₂ : Sub Δ Θ) (σ₃ : Sub Γ Δ) → 
        ((σ₁ ○ σ₂) ○ σ₃) ≡ (σ₁ ○ (σ₂ ○ σ₃))  
  sub-id : τ [ id ]ₜ ≡ τ 
  -- and many more...
``` 


But this directly contradicts the disjointedness of constructors. 
It does not take much reasoning to see our sin: 

```agda 
whoops : ∀ {τ : Type Δ} → (⊥ {lzero}) 
whoops {τ = τ} with (sub-id {τ = τ})
... | () 
``` 

What is the way around this? Altenkirch and Kaposi postulate these identities, and therefore must necessarily postulate the data types... and their eliminators. Eesh!


## Variables 

Variables are De Bruijn indices that find a type in a context. A pain point: We should have that Γ ⊢ τ, which means the zero'th De Bruijn variable must be weakened.

```agda 
data Var where 
  `0  : Var (Γ , τ) (τ [ (π₁ id) ]ₜ)
  `S_ : Var (Γ , υ) τ → Var Γ υ
``` 

## Terms 

The little experiment begins to explode now. We will need this provably false identity:

```agda
postulate 
  sub-id : τ [ id ]ₜ ≡ τ 
```   

Now observe in the type of the application `M · N` that the return type should be `υ [N / 0 ]`. We express this as the substitution `id ▹ N`. However, `N`  hasn't the right type! Rather, the substitution expects `N` to have type 
`Term Γ (τ [ id ]ₜ)`.  Hence the postulate above.

```agda 
data Term where 
  `λ : Term (Γ , τ) υ → Term Γ (Π τ υ)
  _·_ : (M : Term Γ (Π τ υ)) → 
        (N : Term Γ τ) → 
        Term Γ (υ [ id ▹ tr (Term Γ) (sub-id ⁻¹) N ]ₜ)
``` 

Danielsson gets around this by introducing a constructor `sub` for single-term substitutions. I'm not sure I'm on a warpath to solving this right now. It's sufficient to demonstrate the problem, which helps us understand the motivation for QIITs and Cubical Agda.

Missing form the type syntax is a type conversion rule, but we have not defined type equality.
