# Categorical Reconstruction of a reduction free normalization proof 

The following is some scratch paper, in essence, for working through
- Altenkirch et al. **Categorical Reconstruction of a reduction free normalization proof**.
  - https://people.cs.nott.ac.uk/psztxa/publ/ctcs95.pdf
This paper is a *baby step* towards:
- THORSTEN ALTENKIRCH AND AMBRUS KAPOSI 2017. **Normalization By Evaluation For Type Theory In Type Theory**. 
   - https://arxiv.org/pdf/1612.02462
 

The intent of this file is to better understand the presheaf model of intrinsically well-typed
syntax. 

These notes are very rough, not edited, and 
not really intended for others' consumption.

## Other Resources 
- Principles of Dependent Type Theory. Carlo Angiuli and Daniel Gratzer.
  - https://www.danielgratzer.com/papers/type-theory-book.pdf

```agda 
module Categories.TypeTheory.STLC.ReductionFree where 
open import Categories.TypeTheory.STLC.Syntax hiding (Renaming ; ren ; lift ; Substitution ; lifts ; sub ; idSub ; extend ; _β[_]) 
``` 

# Substitution as contravariant 

The first subtlety we have to address is co/contra-variance 
in renamings and substitutions. In `Syntax.agda`, we defined
a renaming as 

```notAgda
Renaming : ∀ (Γ Δ : Context) → Set 
Renaming Γ Δ = ∀ {τ} → Var Γ τ → Var Δ τ 
``` 

But this doesn't fit with the *presheaf* model, as now renaming
is covariant over the context:

```notAgda 
ren : Renaming Γ Δ → Term Γ τ → Term Δ τ 
``` 

I have spent quite a lot of energy in understanding why Hoffmann (originally)
and (now) the broader community have chosen to define the 
arrows of **Ren**, e.g, a renaming `ρ : Renaming Γ Δ`, 
as describing a mapping from the variables in Δ to the variables in Γ. 
This leads to renaming as a **contravariant functor**. For example, in Hoffmann's work we
presume a category of contexts where the objects are of the form  Δ := x₁: σ₁, ... , xₙ : σₙ and the 
arrows f := M₁, ..., Mₙ, written Γ ⊢ f ⇒ Δ, are "context morphisms" from Γ to Δ if we have:
- Γ ⊢ M₁ : σ₁ 
- Γ ⊢ M₂ : σ₂[M₁/x₁]
- ... 
- Γ ⊢ Mₙ : σₙ[M₁/x₁][M₂/x₂]...[M_{n - 1}/x_{n - 1}]. 

This leads to substitution as a contravariant functor---but we could 
just have easily described the opposite category, without any inherent
logical failing. 


## Conceptual intuitions for contravariance 

### The propositional intuition 

The choice of order is argued by Angiuli and Gratzer as follows:
> ... contexts are lists of hypotheses, and a substitution Δ ⊢ γ : Γ 
> states that we can prove all the hypotheses of Γ using the hypotheses 
> of Δ. Thus anything that is true under the hypotheses of Γ
> is also true under the hypotheses of Δ---hence the contravariance of the
> substitution operation.


### The topological intuition

We can also view context categories as "spaces of environments". Then the morphism f : Δ → Γ 
represents the idea that "Δ is an extension of (or has all the variables of) Γ." That is, f is a *projection*
down from Δ to Γ. This is maybe the key intuition, which aligns with the topological definition:
f : Δ ⇒ Γ projects from Δ to Γ. Then the map from variables in Γ to variables in Δ are *injections*
or embeddings into Δ: For each (x : τ) ∈ Γ, we can provide a (y : τ) ∈ Δ.

### The environment translation intuition 

We can view a substitution from Δ to Γ (a tuple 
of terms in Δ for each variable in Γ) as an 
*environment translator*. The key is to view this
with respect to evaluation: Given an environment for Δ, 
I can evaluate the substitution to produce
an environment for Γ. 

Let's explicate this. Define substitutions contravariantly.

```agda
module _ where private 
  open import Data.Unit
  open import Data.Product
  open import Function 
  open import Relation.Binary.PropositionalEquality 

  Substitution : Context → Context → Set
  Substitution Δ Γ = ∀ {τ} → (Var Γ τ) → Term Δ τ 
  postulate 
    sub : Substitution Δ Γ → Term Γ τ → Term Δ τ
``` 

Now, translate from ⟦ Δ ⟧ to ⟦ Γ ⟧:

```agda 
  postulate 
    ⟦_⟧t : Type → Set 

  ⟦_⟧ctx : Context → Set 
  ⟦ ∅ ⟧ctx = ⊤
  ⟦ Γ , x ⟧ctx = ⟦ Γ ⟧ctx × ⟦ x ⟧t 

  postulate 
    ⟦_⟧ : Term Δ τ → ⟦ Δ ⟧ctx → ⟦ τ ⟧t

  ⟦_⟧σ : {Δ : Context} → 
              Substitution Δ Γ → 
              ⟦ Δ ⟧ctx → ⟦ Γ ⟧ctx
  ⟦_⟧σ {∅} {Δ} σ d = tt
  ⟦_⟧σ {Γ , τ} {Δ} σ d = 
    ⟦_⟧σ {Γ} (σ ∘ `S_) d , ⟦ σ `0 ⟧ d
``` 

In other words, evaluation of contexts is inherently
contravariant: We have that `⟦_⟧ctx : Context → Set`
is a functor from our context category to Set. The
arrows are substitutions Γ ⇒ Δ, and `translate` is
the arrow mapping: `⟦_⟧ctx` induces a map from 
Γ ⇒ Δ to ⟦ Γ ⟧ → ⟦ Δ ⟧. 

Furthermore, given M : Term Δ τ we have ⟦ M ⟧ : ⟦ Δ ⟧ctx → ⟦ τ ⟧. If I have a substitution for M, σ : Substitution Δ Γ, then I should expect to be able to evaluate σ 
and apply it to M. 

```
  module _ (M : Term Γ τ) (σ : Substitution Δ Γ) where 
    _ : ⟦ Δ ⟧ctx → ⟦ τ ⟧t
    _ = ⟦ M ⟧ ∘ ⟦ σ ⟧σ 
``` 

We should also expect this semantic substitution to commute with syntactic substitution. This is the substitution lemma. I believe this is specifically why you want the arrows facing the way they do: so that you can compose ⟦ M ⟧ with ⟦ σ ⟧σ.
```     
    _ : ⟦ M ⟧ ∘ ⟦ σ ⟧σ ≡ ⟦ sub σ M ⟧
    _ = {!   !} 
``` 



### The Yoneda Lemma is the Kripke function space 

I have never noticed this before, until now. In my Rω NbE work, 
we evaluate the function space (κ₁ `→ κ₂) into the Kripke function space 
∀ (ρ : Renaming Δ₁ Δ₂) → SemType Δ₂ κ₁ → SemType Δ₂ κ₂:

```notAgda 
SemType Δ₁ (κ₁ `→ κ₂) = 
  (∀ {Δ₂ : KEnv} → (r : Renamingₖ Δ₁ Δ₂) (v : SemType Δ₂ κ₁) → SemType Δ₂ κ₂)
``` 

Let's rephrase this in terms of the STLC, for simplicity. That is, suppose
we have an interpretation function ⟦_⟧ : Type → Env → Set such that 
```notAgda
⟦ τ₁ `→ τ₂ ⟧ Γ = (∀ ρ : Renaming Γ Δ) → ⟦ τ₁ ⟧  Δ → ⟦ τ₂ ⟧ Δ 
```  

We work in a base category **Ren** of contexts and renamings. The Hom-Set Hom(Δ, Γ) is the set of renaming projections of Δ onto Γ. In other words, it's the type `Renaming Γ Δ`. 

```notAgda 
Hom(Δ , Γ) = Renaming Γ Δ = Var Γ τ → Var Δ τ
```

The functor we are describing is from **Ren** to **Set**.
Objects are agda types and morphisms are agda functions.

The functors are presheaves. A presheaf P is a contravariant functor from **Ren** to **Set**. 
- Objects: P(Γ) is a set (e.g., the set of semantic values in context Γ)
- Morphism mapping: Given a morphism f : Δ → Γ (a renaming
  `Renaming Γ Δ`), P maps `f` to a function in Set contravariantly:
  ```notAgda 
  P(f) : P(Γ) → P(Δ)
  ``` 
  For example, view the type `λ X → Term X τ` as a functor. Then `ren : Renaming Γ Δ → Term Γ τ → Term Δ τ` is a presheaf. 

There is a presheaf category [**Ren**ᵒᵖ, Set]:
- Objects are presheaves, like `λ X → Term X τ`;
- Morphisms are natural transformations, e.g, 
  η(Γ) : P(Γ) → Q(Γ) that commutes with the renaming action.

The evaluation function is a presheaf. 
We have that ⟦_⟧ : Env → Type → Set, so,
more specifically, ⟦ τ ⟧ is a presheaf **Ren**ᵒᵖ → Set 
for each type τ. We must also have that ⟦_⟧ maps arrows, requiring:

```notAgda 
renSem : Renaming Γ Δ → ⟦ τ ⟧ Γ → ⟦ τ ⟧ Δ 
``` 

If this is true (it is), then ⟦ τ ⟧ forms a presheaf. 

### Natural transformations of presheaves 

Actually, a natural transformation from Term — τ to ⟦ τ ⟧ takes an object Γ : Env and returns an arrow 
Term Γ τ → ⟦ τ ⟧ Γ. This is precisely `eval` in NbE! 
Likewise, reification has the type
```notAgda 
reify : ⟦ τ ⟧ Γ → NormalTerm Γ τ
```
and so reification is a natural transformation. Both
are subject to naturality conditions. For reify,
we must have for `ρ : Renaming Γ Δ`, that:
```notAgda 
        reify(Γ)
⟦ τ ⟧ Γ ------------> NormalTerm Γ τ
  |                   |
  |                   |
  | renSem ρ          | renNF ρ
  |                   |
  v                   v
⟦ τ ⟧ Δ ------------> NormalTerm Δ τ 
        reify(Δ) 
```         
### Back to the Yoneda Lemma 

To return to intuition: we can evaluate
the STLC into any CCC. One such CCC is 
[**Ren**ᵒᵖ, Set], the category of renaming presheaves.

Recall that we map types into objects in the CCC: 
```notAgda 
  ⟦_⟧t : Type → Obj 
  ⟦ τ₁ `→ τ₂ ⟧t = ⟦ τ₂ ⟧t ^ ⟦ τ₁ ⟧t 
  ⟦ `⊤ ⟧t = 𝕋
  ⟦ τ₁ `× τ₂ ⟧t = ⟦ τ₁ ⟧t × ⟦ τ₂ ⟧t   
``` 

Here the objects are presheaves, so we must map `⟦ τ ⟧t` 
to a presheaf. Specifically, we must map it to the exponential object
in the presheaf category. That is, we must have 
```notAgda 
⟦ τ₁ `→ τ₂ ⟧t = ⟦ τ₂ ⟧t ^ ⟦ τ₁ ⟧t 
``` 

Hence our task is to define what `_^_` is in the presheaf category. To derive a definition, we use the Yoneda Lemma. 

The (contravariant) Yoneda Lemma states that 

```notAgda
F(Γ) ≃ Nat(Hom(Γ,—), F) 
``` 

for any presheaf F. 

Given arbitrary presheaves P and Q in [**Ren**ᵒᵖ, Set],
write `P ⇒ Q` for the exponential object. Then Yoneda states that:

```notAgda
(P ⇒ Q)(Γ) ≃ Nat(Hom(—, Γ), P ⇒ Q) 
``` 
Because [**Ren**ᵒᵖ, Set] is Cartesian closed, 
there is an adjunction between products and exponentials.
Recall that this means, for CCC 𝒞, that 
```notAgda
Hom(X × Y, Z) ≃ Hom(X , Y ⇒ Z)
``` 

Here our hom-sets are natural transformations, hence
```notAgda 
Nat(Hom(—, Γ), P ⇒ Q) ≃ Nat(Hom(—, Γ) × P, Q)
``` 

Unfolding the definition of a natty transform yields an 
arrow for each Δ:

```notAgda 
∀ Δ → Hom(Δ, Γ) × P Δ → Q Δ
``` 

Unpacking the definition of Hom(Γ , Δ) and currying yields:

```notAgda 
∀ Δ → Renaming Γ Δ → P Δ → Q Δ
``` 

Now we let P = ⟦ τ₁ ⟧ and Q = ⟦ τ₂ ⟧, and we have:

```notAgda 
∀ Δ → Renaming Γ Δ → ⟦ τ₁ ⟧ Δ → ⟦ τ₂ ⟧ Δ 
``` 

### Putting the puzzle together
We are trying to define the semantics of the STLC
as a CCC. We choose the CCC [**Ren**ᵒᵖ,  Set] of 
presheaves. The "formula" for evaluating types is already predefined:

```notAgda 
⟦ τ₁ `→ τ₂ ⟧t = ⟦ τ₂ ⟧t ^ ⟦ τ₁ ⟧t 
``` 

Hence a suitable definition of `⟦_⟧` should equal the above. This amounts to defining an exponential object 
in the category of presheaves. In other words, given
presheaves P and Q, we must define an object (that is, a presheaf) that behaves like the exponential P ⇒ Q. The Yoneda Lemma forced our hand: we proved, for arbitrary presheaves P ⇒ Q, that: 

```notAgda 
(P ⇒ Q)(Γ) = ∀ Δ → Renaming Γ Δ → P Δ → Q Δ
``` 
Hence it is precisely correct to define ⟦_⟧ over 
arrows in the STLC as: 

```notAgda 
⟦ τ₁ `→ τ₂ ⟧ Γ = ∀ Δ → Renaming Γ Δ → ⟦ τ₁ ⟧ Δ → ⟦ τ₂ ⟧ Δ
``` 
 