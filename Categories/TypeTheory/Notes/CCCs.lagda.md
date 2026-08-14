```agda
module Categories.TypeTheory.Notes.CCCs where

open import Agda.Primitive
open import Function
open import Relation.Binary.PropositionalEquality hiding (J)
``` 

# Cartesian Closed Categories: Models for the STLC 

A basic interpretation of λ-theories as CCCs, following Awodey.
- https://awodey.github.io/typetheory/notes/typetheory.pdf

This Agda development witnesses a well-known correspondence 
between Cartesian Closed Categories (CCCs) and the STLC with 
unit and product types. This correspondence is described
well in Awodey (above) as well as Pierce. 

The gist is that types and contexts in the λ-calculus can be interpreted
as objects in a particular type of category; terms (or, more specifically,
inferences of the form Γ ⊢ M : τ) are then interpreted as arrows 
from the object denoted by Γ to the object denoted by τ. 

A Cartesian closed category is a category that admits finite products,
exponentials, and a terminal object.  There exists a valid denotation from 
the lambda calculus into any arbitrary CCC. For example, `Set` is a CCC in Agda,
with products given by Σ-types, exponentials given by Π-types, and the unit 
type as a terminal object.

We don't exhibit it in this note, but this relationship is **sound and complete**:
given any flavor of λ-theory (that is, a lambda calculus with additional base types and constants), 
we may denote into a given CCC. And, vice versa, a given CCC has an **internal logic**---
a corresponding lamda calculus. Cool stuff. 

To establish such a result, one must describe an equational theory of the STLC as well 
as the rules governing a given λ-theory's constants. This complicates the development dramatically.
We distinguish an *interpretation* of a λ-theory from a *model* insofar 
that a model respects an equational theory. Hence for now we're
simply interested in interpretations.

## Disregarding λ-theories

A λ-theory 𝕋, as per Awodey, should additionally have 
- a set of basic types B, and 
- A set of constants cᵢ : Cᵢ 
subject to a set of equations between closed terms 
- E = (uₖ ≡ vₖ : Aₖ) 
which we'll forego, for the foremost reason that this 
would mean introducing an equational theory Γ ⊢ M ≡ N : A, 
which would further mean introducing syntactic β-substitution
as an equational rule and showing it is sound w.r.t. 
denotation. These are all things, of course, I have done 
in my own work on Rω, but is quite involved and distracts 
from the main theoretical investigation of interpreting
type theories categorically.

## Syntax 

The syntax of the STLC is entirely standard for intrinsic mechanization.

```agda 
module Syntax where 
``` 

We have arrow types, product types, and the unit type.
```agda 
  data Type : Set where 
      _`→_ : Type → Type → Type 
      `⊤ : Type 
      _`×_ : Type → Type → Type 

  variable 
    τ υ : Type 
``` 

Contexts are right-growing lists of types. 
    
```agda 
  data Context : Set where 
    ∅ : Context 
    _,_ : Context → Type → Context

  variable 
    Γ Δ : Context
```

Variables are intrinsically well-scoped De Bruijn indices. 
The gist is: a variable describes *a location* in a context.

```agda 
  data Var : Context → Type → Set where 
    `0 : Var (Γ , τ) τ 
    `S : Var Γ υ → Var (Γ , τ) υ
``` 

Terms are intrinsically typed typing judgments. The arguments
to each constructor are precisely the premises to the typing judgments
of the STLC.

```agda 
  data Term : Context → Type → Set where 
    ` : Var Γ τ → Term Γ τ 
    `λ : Term (Γ , τ) υ → Term Γ (τ `→ υ)
    _·_ : Term Γ (τ `→ υ) → Term Γ τ → Term Γ υ 
    fst : Term Γ (τ `× υ) → Term Γ τ 
    snd : Term Γ (τ `× υ) → Term Γ υ 
    _,_ : Term Γ τ → Term Γ υ → Term Γ (τ `× υ) 
    ⋆ : Term Γ `⊤
``` 

## An interpretation in Set

It will be most illustrative to first interpret the STLC 
into Set, and then generalize to arbitrary CCC.

```agda 
module SetModel where 
  open Syntax 
  open import Data.Nat   
  open import Data.Unit 
  open import Data.Product renaming (proj₁ to π₁ ; proj₂ to π₂)
``` 
The universe `Set` is effectively a CCC:
- ⊤ is the terminal object;
- The function space (A → B) is the exponential Bᴬ; and 
- The product type `_×_` forms finite products. 

```agda 
  ⟦_⟧t : Type → Set 
  ⟦ τ₁ `→ τ₂ ⟧t = ⟦ τ₁ ⟧t → ⟦ τ₂ ⟧t
  ⟦ `⊤ ⟧t = ⊤
  ⟦ τ₁ `× τ₂ ⟧t = ⟦ τ₁ ⟧t × ⟦ τ₂ ⟧t 
``` 

Contexts are interpreted as products in Set; the empty 
context is interpreted as the terminal object.

```agda    
  ⟦_⟧ctx : Context → Set 
  ⟦ ∅ ⟧ctx = ⊤
  ⟦ Γ , x ⟧ctx = ⟦ Γ ⟧ctx × ⟦ x ⟧t
``` 

The i'th variable is interpreted as the i'th projection:
- ⟦ x₀ : A₀ , ... , xₙ : Aₙ ⟧ = πᵢ : ⟦ Γ ⟧ → ⟦ Aᵢ ⟧

```agda  
  ⟦_⟧v : Var Γ τ → ⟦ Γ ⟧ctx → ⟦ τ ⟧t 
  ⟦ `0 ⟧v = π₂ 
  ⟦ `S x ⟧v = ⟦ x ⟧v ∘ π₁
``` 

The following helpers correspond to the categorical constructions for arrows into a 
product: 

```agda 
  _,,_ : ∀ {ℓ}{A B C : Set ℓ} → 
            (A → B) → 
            (A → C) → 
            A → B × C
  (f ,, g) a = (f a , g a) 
```
and the evaluation arrow of exponentiation: 
```agda 
  ε : ∀ {A B : Set} → (A → B) × A → B 
  ε (f , x) = f x 
``` 
We are careful to describe the denotation without 
introducing the environment η : ⟦ Γ ⟧ctx explicitly.
When denoting terms into a CCC, we will need 
to produce arrows in ⟦ Γ ⟧ctx `→ ⟦ τ ⟧t where 
`_→_` forms arrows in the category. That is to say,
we will not have an explicit function space to work with 
outside the category Set. 

```agda 
  ⟦_⟧ : Term Γ τ → ⟦ Γ ⟧ctx → ⟦ τ ⟧t 
  ⟦ ` x ⟧ = ⟦ x ⟧v
  ⟦ `λ {τ = τ} M ⟧ = curry ⟦ M ⟧ 
  ⟦ M · N ⟧  = ε ∘ (⟦ M ⟧ ,, ⟦ N ⟧)
  ⟦ fst M ⟧ = π₁ ∘ ⟦ M ⟧
  ⟦ snd M ⟧ = π₂ ∘ ⟦ M ⟧
  ⟦ ⋆ ⟧ = const tt 
  ⟦ M , N ⟧ = ⟦ M ⟧ ,, ⟦ N ⟧ 
``` 

## CCCs, formally 

Next we'll parameterize a CCC as a record. 

```agda 
module CCC where 
  private
    variable
      ℓ ℓ₁ ℓ₂ : Level 
``` 

We'll define a CCC as a category with products, a terminal object,
and exponentials. Because I am not immediately planning to prove
any model sound w.r.t. the equational theory of STLC, I am not 
going to pollute definitions with the particular laws and universal
properties of products, terminal objects, and exponentials.
Likewise, category laws---e.g., that Id is an identity and arrows 
group associatively---are omitted for the time being. We can't
add these rules without also introducing a setoid equivalence 
`_≈_` on arrows, at which point the development becomes 
considerably messier. 

For a proper treatment of categories, see either
the [Agda Categories](https://github.com/agda/agda-categories) 
or my library [here](github.com/iowaFP/CategoriesInAgda).

```agda 
  record CCC : Set (lsuc ℓ) where 
    -- Category attributes
    infixr 4 _⇒_
    field 
      Obj : Set ℓ 
      _⇒_ : Obj → Obj → Set ℓ
      _○_ : ∀ {A B C : Obj} → B ⇒ C → A ⇒ B → A ⇒ C 
      -- The identity arrow on object A
      Id : ∀ {A}  → A ⇒ A
  
    -- Terminal object 
    field 
      ⊤ : Obj 
      ! : ∀ (A : Obj) → A ⇒ ⊤ 

    -- Products  
    infixr 5 _×_ 
    field
      _×_ : Obj → Obj → Obj
      π₁ : {A B : Obj} → A × B ⇒ A 
      π₂ : {A B : Obj} → A × B ⇒ B
      ⟨_,_⟩ : {A B C : Obj} → A ⇒ B → A ⇒ C → A ⇒ B × C 
    
    -- exponentials
    infixr 3 _—→_ 
    field 
      _—→_ : (Z Y : Obj) → Obj 
      `eval : ∀ {Z Y : Obj} → (Y —→ Z) × Y ⇒ Z 
      `curry : ∀ {X Y Z : Obj} → X × Y ⇒ Z → X ⇒ (Y —→ Z) 
``` 

We will now parameterize a module by a CCC and show that the STLC has a 
valid denotation into the objects and arrows of this category.

```agda 
  module CCCModel {ℓ} (𝒞 : CCC {ℓ}) where 
    open CCC 𝒞 
    open Syntax 

    ⟦_⟧t : Type → Obj 
    ⟦ τ₁ `→ τ₂ ⟧t = ⟦ τ₁ ⟧t —→ ⟦ τ₂ ⟧t
    ⟦ `⊤ ⟧t = ⊤
    ⟦ τ₁ `× τ₂ ⟧t = ⟦ τ₁ ⟧t × ⟦ τ₂ ⟧t   
```
    
Contexts are interpreted into products; the empty context into the terminal object.
    
```agda     
    ⟦_⟧ctx : Context → Obj 
    ⟦ ∅ ⟧ctx = ⊤
    ⟦ Γ , x ⟧ctx = ⟦ Γ ⟧ctx × ⟦ x ⟧t
``` 

The i'th variable is interpreted as the i'th projection:
- ⟦ x₀ : A₀ , ... , xₙ : Aₙ ⟧ = πᵢ : ⟦ Γ ⟧ → ⟦ Aᵢ ⟧

Note here we are officially interpreting variables into *arrows* in the category,
and not into Set's function space.

```agda  
    ⟦_⟧v : Var Γ τ → ⟦ Γ ⟧ctx ⇒ ⟦ τ ⟧t
    ⟦ `0 ⟧v = π₂ 
    ⟦ `S x ⟧v = ⟦ x ⟧v ○ π₁
``` 

Terms are now denoted into arrows, likewise. The definition
barely differs from our denotation into Set---precisely
because we were careful to define the denotation into Set point-free! 

```agda 
    ⟦_⟧ : Term Γ τ → ⟦ Γ ⟧ctx ⇒ ⟦ τ ⟧t 
    ⟦ ` x ⟧ = ⟦ x ⟧v
    ⟦ `λ {τ = τ} M ⟧ = `curry ⟦ M ⟧ 
    ⟦ M · N ⟧  = `eval ○ ⟨ ⟦ M ⟧ , ⟦ N ⟧ ⟩ 
    ⟦ fst M ⟧ = π₁ ○ ⟦ M ⟧
    ⟦ snd M ⟧ = π₂ ○ ⟦ M ⟧
    ⟦_⟧ {Γ = Γ} ⋆ = ! ⟦ Γ ⟧ctx 
    ⟦ M , N ⟧ = ⟨ ⟦ M ⟧ , ⟦ N ⟧ ⟩ 
``` 

# Further work 

- I could bother to add proper λ-theories.
- I could also bother to introduce an equational theory for the STLC,
  and then prove (at least) soundness and (maybe) completeness.
- It would be interesting to give a denotation of a dependent type theory
  as a Category with Families---or as a Locally Cartesian Closed Category.
  This development is dramatically more involved, as we must represent contexts 
  as their own category, with substitutions as morphisms.

# Works cited 
- Benjamin Pierce. Basic Category Theory for Computer Scientists. 1991.
  - https://direct.mit.edu/books/monograph/3949/Basic-Category-Theory-for-Computer-Scientists
- Steve Awodey. Notes on Type Theory. 2025. 
  - https://awodey.github.io/typetheory/notes/typetheory.pdf