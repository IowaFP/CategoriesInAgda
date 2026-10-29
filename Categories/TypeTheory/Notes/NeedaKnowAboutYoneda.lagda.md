# What You Needa Know About Yoneda: Profunctor Optics and the Yoneda Lemma (Notes)
Guillame Boisseau, Jeremy Gibbons. 

*Notes on "What you Needa Know about Yoneda" for presentation to the CLC seminar, Monday, Nov 2, 2026*.

```agda
module Categories.TypeTheory.Notes.NeedaKnowAboutYoneda where

open import Level 
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality as Eq 
    renaming ([_] to [[_]]) hiding (naturality)
open import Categories.TypeTheory.HoTT
open import Data.String hiding (Left ; Right)
open import Data.List using (List ; _∷_ ; [] ; mapMaybe)
open import Data.Nat using (ℕ)
open import Data.Product 
  using (Σ ; Σ-syntax ; _,_ ; _×_)
  renaming (proj₁ to fst ; proj₂ to snd)
open import Data.Sum 
  renaming (_⊎_ to _+_ ; inj₁ to left ; inj₂ to right) 
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Product.Properties using (Σ-≡,≡→≡)

private
  variable
    A B C D S V T : Set
``` 

# Motivation and Background
What you needa know about this paper is that it's a clever framing of a body of work on **optics** (lenses, prisms, and traversals). There is a world in which this paper is simply called "Categorical Semantics of Profunctor Optics". The Yoneda business is charm thrown in. 

With that in mind, we can isolate two thrusts, which I will describe in greater detail below.
1. A gentle exposition of the Yoneda lemma, independently; and
1. Proofs that the profunctor encoding of optics is "just" the Yoneda Lemma

In turn, I think what we can reasonably cover in the seminar is:
1. What are optics, and 
2. what is the Yoneda lemma

# Optics: Lenses, Prisms, and Traversals

```agda 
module Optics where
```

Lenses originate as a PL-centric solution to the "View Update" problem in classical database literature [Foster et al 2007]. The problem: you have a source table S, and a "view" table V derived from data in S. How can we propagate changes to the source from changes to the view? What changes can be propagated? 

Classically, a view is a tuple of partial functions, `get` and `set` subject to well-behavedness conditions.

```agda
  record Lens(S V : Set) : Set where 
      constructor ⟨_,_⟩⟨_,_⟩
      field 
          get : S → V 
          set : S → V → S
``` 

In other words, `get` spawns a view from the source, and `set(s, v)` updates source `s` with information from a (possibly updated) view `v`.

A lens is called **well-behaved** if (i) `get` is a retraction of `set s`(get-set), and (ii). These are also known as "round-trip" laws: (i) states that what we put in is what we get out, and (ii) states that what we get is what's put back in. 

```agda         
          get-set : ∀ s → get ∘ (set s) ∼ id
          set-get : ∀ s → (set s) (get s) ≡ s 
``` 

A lens is called **very well-behaved** if it additionally satisfies a "set-set" law: 

```agda
  record VeryWellBehaved (ℓ : Lens S T) : Set where 
    constructor VWB
    open Lens ℓ
    field
      set-set : ∀ s v₁ v₂ → set (set s v₁) v₂ ≡ set s v₂
``` 

which states that the effect of a sequence of two sets is just the effect of the second. 

## Lenses for easier immutable data treatment 
The allure of lenses is critically that they are **composable**. The flagship application of lenses (as used in the Haskell library) is that they make (in-place) access and update to nested records easier.

From the Haskell lens library:

```hs
data Atom = Atom { _element :: String, _point :: Point }
data Point = Point { _x :: Double, _y :: Double }
``` 
If you wanted to increase the x coordinate of an Atom by one unit, you would have to write something like this in Haskell:
```hs
shiftAtomX :: Atom -> Atom
shiftAtomX (Atom e (Point x y)) = Atom e (Point (x + 1) y)
``` 
This unpacking and repacking of data types grows increasingly difficult the more fields you add to each data type or the more deeply nested your data structures become.

The lens library solves this problem by letting you instead write:
```hs
{-# LANGUAGE TemplateHaskell #-}

import Control.Lens hiding (element)
import Control.Lens.TH

data Atom = Atom { _element :: String, _point :: Point } deriving (Show)

data Point = Point { _x :: Double, _y :: Double } deriving (Show)

$(makeLenses ''Atom)
$(makeLenses ''Point)

shiftAtomX :: Atom -> Atom
shiftAtomX = over (point . x) (+ 1)
``` 



## Prisms and traversals

Lenses were eventually generalized to prisms, which permit the view/update of variants, and traversals, which permit the view/update of an arbitrary number of values. For example, a prism can be defined as:

```agda
  open import Data.Maybe renaming (map to _*)
  record Prism(S V : Set) : Set where 
      field 
          match : S → Maybe V
          build : V → S
``` 
subject to variant-flavored round-trip laws:
```         
          match-build : match ∘ build ∼ just
          build-match : build * ∘ match ∼ just 
```

Traversals are, generally speaking, a way to apply a get or set operation over multiple values. For example, pairs. From the Lens library:

```hs
traverse :: Traversal' (Pair a) a
over traverse :: (a -> a) -> (Pair a -> Pair a)
over traverse (+ 1) (Pair 3 4) = Pair 4 5
```

A traversal may be defined as: 

```agda 
record Traversal ( S V : Set) : Set where 
  field 
    toListOf : S → List V 
    over : (V → V) → S
```


## The problem(s)

The kicker is this: the straightforward definitions (above) of lenses, prisms, and traversals:
1. are not sufficiently general, and 
2. do not compose with one another.

### Polymorphic optics 

Problem #1 is why the Yoneda paper defines a **lens** of type `Lens a b s t` as providing "access via a getter and a setter onto a component of type A within a composite product structure of type S, allowing the component to be replaced by one of type B, yielding a new composite of type T". 

```hs
data Lens s t a b = Lens { view :: s → a, update :: s × b → t} 
``` 

The generalization here is that a view could reasonably be a single attribute of a record (the type `a`) and not a projection (the type `t`), and we might choose to update the source with different data than `a` to yield a source with a new type `t`. The generality permits type-changing operators, e.g., changing  a `(String, Int)` pair to `(Bool , Int)`: 

```rosi 
updateFst : Lens (String, Int) (Bool, Int) String Bool
``` 
Under the straightforward definition, we would have: 
- `view :: (String, Int) → String`, and 
- `update :: (String, Int) × Bool → (String, Bool)`

What does this lens do, then? It grabs and updates the second component but, crucially, changes the type of this component from String to Bool. You can imagine how this might be helpful in the database context when considering schema transformations.

### Composition

The real pain-point is that it's not clear at all how to compose e.g. a lens after a prism, a prism after a lens, a traversal with a lens, and so forth. This is the concrete problem that profunctor optics address. I emphasize this because the optics literature is quite theoretically dense and often dives into the categorical deep end without any explanation or justification. 

Under the Profunctor encoding, every type of optics has the same form:

```agda
record Profunctor (P : Set → Set → Set) : Set₁ where 
  constructor profunctor
  field
    dimap : ∀ {A B C D : Set} → (C → A) → (B → D) → P A B → P C D
open Profunctor {{...}}
```

Categorically, a profunctor from 𝒞 to 𝒟 is a bifunctor (that is, a functor whose domain is a product category) from 𝒟ᵒᵖ × 𝒞 → Set. The typeclass above witnesses this: it is contravariant on its first argument and covariant on the second.  

While seemingly exotic, we are all intimately with one particular profunctor: the arrow type, which is covariant in its return type and contravariant in its argument. 

```agda
dimap→ : ∀ {A B C D : Set} → 
          (C → A) → (B → D) → 
          (A → B) → (C → D)
dimap→ h g f = g ∘ f ∘ h 

_`→_ : Set → Set → Set
A `→ B = A → B

instance
  Profunctor→ : Profunctor _`→_
  Profunctor→ = profunctor dimap→
``` 

What separates each type of optic is a typeclass constraint on the profunctor `p`. A lens is a *Cartesian* profunctor, coherent with products:

```agda 
record Cartesian 
    (P : Set → Set → Set) 
    {{Pf : Profunctor P}} : Set₁ where 
  constructor cartesian 
  field 
    second : ∀ {A B C} → 
             P A B → P (C × A) (C × B)


-- As an aside to Garrett:
-- Should I claim this is a separation algebra?
second→ :  ∀ {A B C : Set} → 
             (A → B) → 
             (C × A) → (C × B)
second→ f (c , a) = (c , f a)

instance 
  Cartesian→ : Cartesian _`→_ 
  Cartesian→ = cartesian second→
```

 
and a Prism is *CoCartesian*:

```agda
record Cocartesian 
    (P : Set → Set → Set) 
    {{Pf : Profunctor P}} : Set₁ where 
  constructor cocartesian 
  field 
    Right : ∀ {A B C} → 
             P A B → P (C + A) (C + B)

-- As an aside to Garrett:
-- Should I claim this is a separation algebra?
right→ :  ∀ {A B C : Set} → 
             (A → B) → 
             (C + A) → (C + B)
right→ f (left c) = left c
right→ f (right a) = right (f a) 

instance 
  Cocartesian→ : Cartesian _`→_ 
  Cocartesian→ = cartesian second→
``` 

What makes profunctor optics fascinating, and what is precisely the purpose of this paper is that: **the straightforward encoding and the profunctor encoding are equivalent.** That is to say, any lens gives rise to a Cartesian Profunctor (and vice versa), and any prism gives rise to a Cocartesian Profunctor (and vice versa). The authors argue that this is "just" the Yoneda lemma. (Which of course, it isn't really just that.) 

# The Yoneda Lemma 

There is a (arguably valid) argument here that Gibbons, a very good writer, has laundered the key result of this paper through musings on the Yoneda lemma. So much so that one can really take away from this paper nothing other than its insights into the Yoneda lemma.

I suspect what happened, strategically, is that [Pickering et al] wrote a rather excellent introduction to the pragmatics of profunctor optics, leaving its categorical foundations on the table. To this day, there is still some categorical excavation being done on profunctors.

That said, let's now muse on the Yoneda Lemma for a few sections.

## Yoneda, formally

The (covariant) Yoneda Lemma states that, for covariant F : 𝒞 → Set and object A ∈ 𝒞,  the *set* of natural transformations between Hom(A, —) and F is in bijection to the set F(A). Gibbons writes:

**Theorem (Yoneda Lemma).** For 𝒞 a locally-small category:
  [𝒞, Set](𝒞(A,—), F) ≃ F(A)
naturally in A ∈ 𝒞 and F ∈ [𝒞, Set]. I'll add that this uses some spiffy notation, and I'm not sure that notation is helping. Let me break it down:
- "Locall small" means hom-sets (the class of arrows between objects) are sets
- [𝒞, Set] is the category of functors from 𝒞 to Set
- We write 𝒞(X,Y) to denote the set (or class) of arrows from objects X, Y ∈ 𝒞. Hence [𝒞, Set](𝒞(A,—), F) is the set of arrows in the functor category [𝒞, Set] between the functors (objects in [𝒞, Set]) 𝒞(A,—) and F. The arrows in [𝒞, Set] are natural transformations, hence the entire term is a set of natural transformations. Because 𝒞 is locally small and F : 𝒞 → Set, its collection of natural transformations is a set.
- Likewise, 𝓒(A,—) denotes the functor sending the object B to the set of arrows 𝒞(A, B) and arrows f : B → C in Hom(𝒞) to an arrow:
  ```no
  𝒞(A , f) : 𝒞(A , B) → 𝒞(A, C) 
  𝒞(A , f)(h) = f ∘ h
  ```
- The phrase "naturally in A ∈ 𝒞 and F ∈ [𝒞, Set]" just means that A and F may vary parametrically.

I Think this is a bit too clever for it's good, and would rather write more clearly:

**Theorem (Yoneda Lemma, á la Alex)**: For 𝒞 a locally-small category, A ∈ Obj(𝒞) and F : 𝒞 → Set:
  Nat(Hom(A, —), F) ≃ F(A) 

## Proof of the Yoneda Lemma 

The Yoneda Lemma is rather tricky to understand because it's so damn general. However, it's actually remarkably simple to prove. 

We'll need some preliminary encodings of functors: and natural transformations.

```agda
record Functor : Set₁ where 
  constructor functor
  field 
    F : Set → Set
    fmap : ∀ {A B : Set} → (A → B) → F A → F B
    fmap-id : ∀ {A} → fmap {A} id ∼ id
    fmap-compose : ∀ {A B C} → 
                  (f : B → C) (g : A → B) → 
                  fmap (f ∘ g) ∼ fmap f ∘ fmap g 
       
  _₀ : Set → Set
  _₀ = F
  _₁ : ∀ {A B : Set} → (A → B) → F A → F B
  _₁ = fmap 
open Functor using (_₀ ; _₁)
``` 

Just some clever module hackery so that `Open Gunctor G` names F to G, fmap to gmap, and so forth:

```agda
module Gunctor (𝔾 : Functor) where 
  open Functor 𝔾 renaming 
    ( F to G 
    ; fmap to gmap 
    ; fmap-id to gmap-id 
    ; fmap-compose to gmap-compose) public
``` 

Now hom-functors are arrows in Set. 

```agda
Hom[_,—] : Set → Functor
Hom[ A ,—] = functor
  (λ X → (A → X))
  (λ f → f ∘_)  
  refl-∼ 
  λ _ _ → refl-∼
```  

Define naturality between functors:

```agda
  -- We will need to use naturality: 
  -- 
  --          η(X)
  -- (A → X) ---------> F x 
  --    |                |
  --    | (f ∘_)         | fmap f 
  --    |                |
  -- (A → Y) --------->  F y
  --           η(Y)
Naturality : ∀ (𝔽 𝔾 : Functor) → 
              (∀ (X : Set) → (𝔽 ₀) X → (𝔾 ₀) X) → Set₁
Naturality 𝔽 𝔾 η = ∀ (X Y : Set) (f : X → Y) → gmap f ∘ η X ∼ η Y ∘ (fmap f)
  where 
      open Functor 𝔽
      open Gunctor 𝔾 
```

  The set of natural transformations from F to G is thus:

```agda
Nat[_,_] : (𝔽 𝔾 : Functor) → Set₁
Nat[ 𝔽 , 𝔾 ]  = Σ[ η ∈ (∀ (X : Set) → F X → G X) ] (Naturality 𝔽 𝔾 η)
  where open Functor 𝔽 ; open Gunctor 𝔾
```     

Now the Yoneda lemma is natural (i.e., parametric in) A and F: 

```agda
module _ (A : Set) 
         (𝔽 : Functor) where 

  open Functor 𝔽
``` 

We must define a map between the sets Nat(Hom(A,—), F) and F(A).
In the left to right direction, we have
  η : (X : Set) → (A → X) → F X 
and so 
  η A : (A → A) → F A 
and thus we can simply use the identity to get:
  η A id : F A 

which is precisely what we do.

```agda 
  yoneda→ : Nat[ Hom[ A ,—] , 𝔽 ] → 
            F A                
  yoneda→ η = η .fst A id
``` 


In the other direction, we have x : F A, and need to build a natural transformation 
  η : (X : A) → (f : A → X) → F X.
If we bring X and f into scope, then 
  fmap f : F A → F X 
and hence 
  fmap f x : F X
as desired.

```agda
  yoneda← : F A → 
            Nat[ Hom[ A ,—] , 𝔽 ]
  yoneda← x = (λ X f → fmap f x) , λ X Y f g → sym (fmap-compose f g x) 
``` 

We now need to demonstrate that these two are mutually inverse. Going from F A → Nat(Hom(A, —), F) → F A is straightforward. For any x : F A, we have:
```no
    yoneda→ (yoneda← x) 
  = yoneda→ (λ X f → fmap f x , ...) 
  = (λ X f → fmap f x , ...) .fst A id 
  = (λ X f → fmap f x) A id 
  = fmap id x
``` 
and so this is proven simply by the fmap-id property.
  

```agda  
  -- yoneda← is a section of yoneda→
  rinv : yoneda→ ∘ yoneda← ∼ id 
  rinv = fmap-id 
``` 

The other direction, from Nat(Hom(A, —), F) to F A to Nat(Hom(A, —), F) is slightly trickier. Let η ∈ Nat(Hom(A, —), F) . Then:

```no 
    yoneda← (yoneda→ η) 
  = yoneda← (η A id) 
  = λ X f → fmap f (η A id)
  = ...?
  = η
``` 

We need function extensionality to equate `λ X f → fmap f (η A id)` with η. With X : Set and f : A → X be arbitrary, our goal is:

```no 
  fmap f (η A id) ≡ η X f
``` 

for which we must invoke naturality. Naturality states for f : A → X that:
```no
    fmap f ∘ (η A) ∼ η X ∘ (f ∘_) 
``` 

Plugging this definition in the identity gives:

```no 
    fmap f (η A id) 
  ≡ (η X ∘ (f ∘_)) id
  ≡ η X (f ∘ id) 
  ≡ η X f 
``` 

as desired. N.b. 

```agda 
  -- yoneda← is a retraction of yoneda→
  linv : yoneda← ∘ yoneda→ ∼ id 
  linv (η , nat) = Σ-≡,≡→≡ 
      (fun-ext (λ X → fun-ext (λ f → nat A X f id)) , 
      -- Not interested in proving this part
      ⊥-elim pfft)
    where
      postulate pfft : ⊥ 
    
  -- One direction is the fmap identity law; 
  -- the other direction is naturality.
  yoneda-equiv : has-inverse yoneda→
  yoneda-equiv = Inv yoneda← rinv linv
``` 

## Intuitions 

The Yoneda lemma generally hurts your brain. The paper does a great job of trying to wrangle Yoneda back down to earth. Let's sift through the introductory sectons.

### Indirect Inequality


The rule of *indirect order* in a given preorder (A, ≤) states that, for a, b ∈ A: 

```no
(b ≤ a) ⇔ (∀ c. (a ≤ c) ⇒ (b ≤ c))
``` 


The authors argue that this is an instance of the Yoneda embedding in the category Pre(A, ≤), where Pre(A, ≤) has:
- the elements of A as objects, and 
- exactly one arrow between a, b ∈ A iff a ≤ b

That this is a category follows from reflexivity and transitivity of preorders:
- Each element a ∈ A has a ≤ a, and so there exists an identity arrow id : A → A 
- given a, b, c ∈ A, if a ≤ b and b ≤ c then a ≤ c; correspondingly, arrows are closed under composition.

In the left-to right direction, we have that a ≤ a, and so instantiating c to equal a implies b ≤ a.

The other direction employs the Yoneda lemma, where we let b ∈ Pre(A, ≤) be arbitrary and instantiate F to Hom(b, —):

```no
Nat(Hom(a,—), Hom(b, —)) ≃ Hom(b, a) 
``` 

In Pre(A , ≤), the homset Hom(b, a) is a single arrow when b ≤ a and empty otherwise. A natural transformation φ : Hom(a, —) → Hom(b, —) is a family of functions φ(c) : Hom(a, c) → Hom(b, c). But Hom(a, c) and hom(b, c) are either empty or singletons, and so φ(c) just states that an inhabitant of Hom(a, c) implies an inhabitant of Hom(b, c). In other words, that a ≤ c ⇒ b ≤ c. But this immediately implies the claim: instantiating these intuitions into Yoneda:

```no
  Nat(Hom(a,—), Hom(b, —)) ≃ Hom(b, a) 
``` 

immediately yields:

```no
  (∀ c. a ≤ c ⇒ b ≤ c) ⇒ b ≤ a
```

Or, to be more rigorous: the set Hom(b, a) has cardinality 1 if b ≤ a and 0 otherwise. But Yoneda implies a bijection between this set and Nat(Hom(a, —), Hom(b, —)), the set of families φ where φₓ : Hom(a, x) → Hom(b , x). Naturally, if such a family exists, then a ≤ x implies b ≤ x for arbitrary x. Further, we must also have |Hom(b, a)| > 0, meaning b ≤ a, as desired.

### Indirect Equality

A corollary of the Yoneda lemma is that the Yoneda embedding, given by 
- 𝕪 :  𝒞 → [𝒞, Set] 
- 𝕪(X) = Hom(X, —) 
is full and faithful. A functor F : ℂ → 𝒟 is faithful iff it maps hom-sets injectively: if F(f) = F(g) then f = g. It is full iff it is surjective on hom-sets: if h ∈ Hom(𝒟), then there exists g ∈ Hom(𝒞) such that F(g) = h. 

Moreover, full and faithful functors *reflect* isomorphisms. A functor already *preserves* isomorphisms: 

```no 
    f ∘ g = id 
    {F is a functor}
  ⇒ F(f ∘ g) = F(id)
    {functor laws} 
  ⇒ F(f) ∘ F(g) = id
``` 

To go in the other direction (*reflection*) requires injectivity: 

```no 
    F(f) ∘ F(g) = id
    {F is a functor}
  ⇒ F(f ∘ g) = F(id)
    {injectivity} 
  ⇒ f ∘ g = id
``` 

If F(f) is an isomorphism, it might be that its inverse h ∈ Hom(𝒟) is not hit by any arrow in 𝒞. However, if F is full, we know that F(f) ∘ h ∼ id implies h = F(g) for some g ∈ Hom(𝒞), and thus f ∘ g ∼ id: f is an isomorphism.

The Yoneda Embedding 𝕪 is a functor from 𝒞 to the functor category [𝒞, Set]. An arrow in [𝒞, Set] is a natural transformation, and thus an isomorphism in [𝒞, Set] is a natural isomorphism. A natural transformation η on F, G : 𝒞 → Set assigns to each A ∈ Obj(𝒞) a set-arrow f : F(A) → G(A). If that arrow is an isomorphism, then η is called a natural isomorphism. That 𝕪 is faithful gives us: 

```no
   𝕪(A) ≃ 𝕪(B)
⇔ Hom(A, —) ≃ Hom(B, —)
⇔ A ≃ B
``` 

Moreover, the contravariant embedding, given by
- 𝕪ᵒᵖ :  𝒞ᵒᵖ → [𝒞, Set] 
- 𝕪ᵒᵖ(X) = Hom(—, X) 

is also full and faithful, meaning

```no 
   A ≃ B 
⇔ Hom(—, A) ≃ Hom(—, B)
⇔ 𝕪ᵒᵖ(A) ≃ 𝕪ᵒᵖ(B)
``` 

We have to be careful about equality: in a category, we may equate arrows, not objects. (Only a **strict category** has a notion of equivalence on objects.) Rather, we equate objects up to isomorphism: if there exists f : A → B s.t. f has an inverse. Correspondingly, we don't equate functors under extensional equality (that F X = G X for all X ∈ Obj(𝒞)). Two functors are instead equivalent if there exists a natural isomorphism between the two. The premise 𝕪(A) ≃ 𝕪(B) states as such: Hom(A, —) and Hom(B, —) are naturally isomorphic, and concludes as such: the objects A ≃ B are isomorphismic. 

In effect, this set of equivalences means that two objects A, B are "the same" iff they look the same from all viewpoints. In a poset Pos(A, ≤), anti-symmetry implies that a = b if a ≤ b and b ≤ a. If f : a → b is an isomorphism, it is trivially the case that a ≤ b and b ≤ a, and so a = b iff a ≃ b. Moreover, recall that Hom(x, —) maps the object a to the arrow a ≤ x. Its dual (the contravariant hom functor) is easily defined then as the map Hom(—, x)(a) = x ≤ a.  We have that Hom(—, a) ≅ Hom(—, b) if they are naturally isomorphic, and so:

```no 
   Hom(A, —) ≅ Hom(B, —) 
⇔ (∀ c. a ≤ c ⇔ b ≤ c)
⇔ a = b
⇔ (∀ c. c ≤ a ⇔ c ≤ b)
⇔ Hom(—, A) ≅ Hom(—, B) 
``` 

### Currying 

Any category 𝒞 with exponentials (e.g. Set) has products and witness the adjunction:

```no
Hom(A × B, C) ≃ Hom(A, B ⇒ C)           { curry }
``` 

and, if that category admits coproducts, then:

```no 
Hom(A + B, C) ≃ Hom(A , C) × Hom(B, C)   { sum } 
``` 

This latter property simply states that an eliminator e.g. f : A + B → C may be decomposed into two separate eliminators f₁ : A → C and f₂ : B → C. That this is possible for any f : A + B → C---even those not defined via injection---follows from the universal property of sums.

From these two properties, we get the distributivity property:

```no
  Hom((A + B) × C, X) 
  { curry}
≃ Hom(A + B, C ⇒ X)
  { sum }
≃ Hom(A , C ⇒ X) × Hom(B , C ⇒ X) 
  { curry }
≃ Hom(A × C, X) × Hom(B × C, X) 
  { sum }
≃ Hom((A × C) + (B × C), X)
``` 

Since C was natural, we have instead: 

```no 
   Hom((A + B) × —, X) 
≃ Hom((A × —) + (B × —), X) 
``` 

Meaning we may rephrase this according to the functors:
- F(C) = A + B × C
- G(C) = A × C + B × C 

By the rule of indirect equality, we have that:
```no 
   Hom((A + B) × C, X) ≃ Hom((A × C) + (B × C), X)
=  Hom(F(C), —)        ≃ Hom(G(C), —)   
⇔ F(C) ≃ G(C)
``` 

This entails the distributivity law:

```no 
A + B × C ≃ (A × C) + (B × C)
```

I am not categorically wise, but nevertheless the note Gibbons leaves I found helpful, in a sense, to garnering a stronger intuition for limits/colimits:
the only properties employed, above, are that — × 𝒞 is left adjoin to — ⇒ 𝒞, and that + be a colimit. Hence this tinkering proves (albeit in a specific case) that left adjoints preserve colimits.




### Cayley's Theorem

It's well known that Yoneda generalizes Cayley's theorem, which states that every group G is isomorphic to a subgroup of a symmetric group. More specifically, G is isomorphic to a subgroup of the group of permutations on G. A similar statement may be made about monoids.

How does Yoneda imply this? Recall that every monoid M gives rise to a category 𝕄 in which:
- We have one object, ★.
- The identity e is the identity arrow id ∈ Hom(𝕄)
- Each element x ∈ M is an arrow x′ : ★ → ★ in 𝕄.
- the composition of arrows x′ y′ ∈ 𝕄 is equal to (xy)′. 
  That is, given x, y, z in M with corresponding arrows x′, y′, z′ ∈ 𝕄, 
  we have
   x′ ∘ y′ = z′ iff xy = z.

That this is a category follows from the associativity and identities of the monoid. A groupoid is a category in which every arrow is an isomorphism, and so, correspondingly, every group is a groupoid.

Cayley's theorem for groups says:

**Theorem (Cayley's).** Every group G is isomorphic to a subgroup of the permutation group on G.

The permutation group on G arise from the set 

{ f ∈ G → G ∣ f bijective }

where function composition is the group operation. How does Yoneda imply Cayley's? We have:
- The functor F maps ★ to some set A and arrows to functions on A. This is clearly a **group action**: it's the group structure of 𝔾 *acting on* the set A. The action laws follow from functor identity and composition.
- Hom(★, —) : 𝔾 → Set is a functor mapping ★ to the hom-set Hom(★, ★)---in
  effect, to the underlying set G. Each arrow x′ ∈ 𝔾 is then mapped by left-composition:
    Hom(★, x′)(y′) = x′ ∘ y′ 
  which corresponds to a permutation via left-multiplication:
    φₓ(y) = xy
  In other words, Hom(★, —) maps each arrow in G to an invertible function on G, and so we can view Hom(★, —) really as φ : G → Perm(G).

What we want to argue is that (1) φ : G → Perm(G) is a group homomorphism and (2) φ is injective, which immediately implies G ≃ Im(φ) and, as Im(φ) ≤ Perm(G), we have Cayley's theorem: every group is isomorphic to a subgroup of permutations on G. 

We view φ as the arrow action of Hom(★, —). That this is a homomorphism follows from the functor properties: Unfolding F(a′ ∘ x′) = F(a′) ∘ F(x′) states φ­ₐₓ = φₐ ∘ φₓ---precisely the homomorphic property. Moreover, each φₓ is invertible via φₓ₋₁, so Im(φ) ≤ Perm(G): each φₓ is a permutation.

Here, the Yoneda embedding maps the object ★ to the functor Hom(★, —) (an object (functor) in [𝔾, Set]) and each arrow x′ ∈ Hom(𝔾) to a natural transformation between Hom(★, —) and itself. But this natural transformation is in fact just the permutation φₓ. That 𝕪 is faithful implies, for any a, x ∈ Hom(𝔾), that
```no 
    𝕪(a′) = 𝕪(x′)
  ⇒ φₐ = φₓ
  ⇒ a = x.
```

This immediatelly implies φ is an injection. Thus 𝔾 ≃ Im(φ). (Every injection f : A → B yields a bijection between A and Im(B).) Moreover, Im(φ) is a subgroup of Perm(G), which proves Cayley's theorem.


## What's left undone 

What I have not covered in depth, unfortunately, is the paper's chief contribution: a derivation of profunctor optics. I've skimmed the construction. The authors invoke the Yoneda Lemma twice to yield the Double Yoneda Embedding, then use that to first show a correspondence between
- (a → b) and ∀ f. Functor f ⇒ f a → f b 
- concrete adapters:
  ```hs 
  data Adapter a b s t = Adapter { from :: s → a, to :: b → t}
  ``` 
  and profunctor adapters
  ```hs
  type AdapterP a b s t = ∀ p. Profunctor p ⇒ p a b → p s t
  ``` 
- concrete (lenses|prisms|etc) and profunctor (lenses|prisms|etc)

The translations require a fair bit of thought to digest but, as far as I can tell, do not invoke any category theory wilder than what we've already discussed. I suspect that there are some existential types, in the derivations, that would correspond to ends and coends. I applaud the authors for not using such language. 
  

# Works Cited


- Guillame Boisseau, Jeremy Gibbons. What You Needa Know About Yoneda: Profunctor Optics and the Yoneda Lemma. 2018. 
  - https://www.cs.ox.ac.uk/jeremy.gibbons/publications/proyo.pdf
- J. Nathan Foster, Michael B. Greenwald, Jonathan T. Moore, Benjamin C. Pierce, Alan Schmitt. Combinators for Bidirectional Tree Transformations: A Linguistic Approach to the View-Update Problem. 2007.
    - https://dl.acm.org/doi/pdf/10.1145/1232420.1232424
- Matthew Pickering, Jeremy Gibbons, and Nicolas Wu. Profunctor Optics: Modular Data Accessors. 2012.
    - https://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/poptics.pdf    
