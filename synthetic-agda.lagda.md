---
pagetitle: Introduction to Synthetic Agda | The Hyrax Project
title: Introduction to Synthetic Agda
author: Corinthia Beatrix Aberlé
---

# Introduction {#intro}

## What is Synthetic Agda? {#what-is}

Synthetic Agda is an extension of the Agda programming language and proof assistant to support advanced forms of [synthetic mathematics](https://golem.ph.utexas.edu/category/2015/02/introduction_to_synthetic_math.html). For this purpose, we extend Agda with various constructions that allow it to be customized to reflect the internal language of any [Grothendieck topos](https://ncatlab.org/nlab/show/Grothendieck+topos) (or, more generally, any [Grothendieck ∞-topos](https://ncatlab.org/nlab/show/(infinity,1)-topos)), and moreover for a broad class of type-theoretic constructions (including inductive types, higher inductive types, coinductive types, adjoint functors, etc.) to be studied in this setting. This is accomplished by extending Agda with various axioms, all of which are given computational rules via Agda's term rewriting system. Perhaps surprisingly, this all can be done by enabling some of Agda's modal features (namely the `--cohesion` and `--flat-split` flags) and then using Agda's mechanisms of postulates and rewrite rules to assert the relevant axioms and their computational rules. As such, Synthetic Agda can be (and has been) implemented as an Agda module, such that making use of Synthetic Agda's features requires merely importing this module. In fact, this document *is* that module, written as literate Agda that also serves as a guide to the features and basic definitions of Synthetic Agda, explaining each in turn as it is introduced.

```agda
{-# OPTIONS --rewriting --cohesion --flat-split 
            --without-K --cubical-compatible #-}
module synthetic-agda where
```

---

# The Atoms of Synthetic Mathematics {#atoms}

## Type Theory {#type-theory}

The base type theory of Synthetic Agda is essentially that of vanilla Agda -- i.e. a form of Martin-Löf Type Theory -- extended with an *interval* and *path types* similar to those of Cubical Type Theory and Cubical Agda, along with the basic modal features supported by Agda's `--cohesion` and `--flat-split` flags. In addition to the interval/path types, we also make use of some definitions from [Homotopy Type Theory](https://homotopytypetheory.org/book/) (although we do not assume univalence), which are specified in the `hott` module.

```agda
open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import hott
```

---

## Theories & Signatures {#sig}

One of the key aims of Synthetic Agda is to provide a type-theoretic setting for working in the internal language of any Grothendieck (∞-)topos. However, since arbitrary Grothendieck (∞-)topoi may be quite complex, we build this synthetic setting up in stages, first identifying a subset of "simple" topoi whose internal languages are relatively easy to axiomatize, and then showing how the internal languages of all other Grothendieck topoi can be obtained as certain subuniverses definable within the internal languages of these *simple* topoi.

For this purpose, we leverage the fact that every Grothendieck topos is the [classifying topos](https://ncatlab.org/nlab/show/classifying+topos) of some [geometric theory](https://ncatlab.org/nlab/show/geometric+theory) (and similarly every Grothendieck ∞-topos is the classifying ∞-topos of some *higher* geometric theory). Now, geometric theories, much like the topoi they represent, can be quite complicated, so at first sight this shift in perspective may not seem to have bought us much progress toward our goal. However, at the syntactic level, it is straightforward to see that every geometric theory consists of two parts: a *signature* of atomic sorts and constants, and a set of *axioms* imposed upon this signature.

A natural choice of "simple" topoi that is suggested by this perspective is then given by the classifying topoi of (higher) geometric theories that *contain no axioms*, i.e. theories that are given solely by their signature. The internal languages of these topoi then turn out to be relatively easy to characterize axiomatically, as we now demonstrate.

A signature for a (higher) geometric theory, as we define it, consists of a set of atomic *sorts* (which may depend upon each other), along with, for each closed atomic sort, a set of *constants* belonging to that sort (note that we do not include function symbols in our signatures, since this would greatly complicate the presentation of what is to follow, and any `n`-ary function symbol in a geometric theory can always be replaced with an `(n+1)`-ary relation symbol/dependent sort, along with axioms stating that this relation is many-one and total).

In order to encode the potential dependence of atomic sorts upon each other, we additionally need a type of *telescopes* consisting of strings of atomic sorts that may depend upon each other. We specify this as an inductive-recursive type `STele`, with two functions `El♮ : STele → Set` and `El♭ : STele → Set`, which decode a telescope to the corresponding types of tuples of elements of their atomic sorts, and the constant elements of these atomic sorts, respectively.

```agda
-- telescopes of atomic sorts
data STele (ℓ : Level) : Setω

-- tuples of elements of the atomic sorts contained in a telescope
El♮ : ∀ {ℓ} → STele ℓ → Set ℓ

-- tuples of constants of the atomic sorts contained in a telescope
El♭ : ∀ {ℓ} → STele ℓ → Set ℓ

-- inclusion of El♭ in El♮
↓ : ∀ {ℓ} {Γ : STele ℓ} → El♭ Γ → El♮ Γ
```

Using this, we then postulate, for each telescope `Γ : STele` and family of types `A : El♭ Γ → Set`, a type `Sort Γ A` with a decoding function `El : Sort Γ A → (x : El♮ Γ) → Set` whose elements represent atomic sorts `J` dependent upon the atomic sorts in `Γ`, such that for each `x : El♭ Γ`, the set of constants of type `El J` evaluated at `x` is `A x`.

```agda
postulate
    -- atomic sorts
    Sort : ∀ {ℓ} (Γ : STele ℓ) → (El♭ Γ → Set ℓ) 
           → Setω

    -- type represented by an atomic sort
    El : ∀ {ℓ} {Γ : STele ℓ} {A : El♭ Γ → Set ℓ} 
         → (J : Sort Γ A) (x : El♮ Γ)
         → Set ℓ

    -- inclusion of constants in each closed atomic sort
    𝐣 : ∀ {ℓ} {Γ : STele ℓ} {A : El♭ Γ → Set ℓ} 
        → (J : Sort Γ A) (x : El♭ Γ)
        → A x → El J (↓ x)
```

We can then complete the definitions of `STele`, `El♮`, `El♭`, and `↓` as follows:

```agda
data STele ℓ where
    emp : STele ℓ
    _,,[_]_ : (Γ : STele ℓ) (A : El♭ Γ → Set ℓ) 
              → Sort Γ A → STele ℓ

El♮ emp = ⊤
El♮ (Γ ,,[ A ] J) = Σ (El♮ Γ) (El J)

El♭ emp = ⊤
El♭ (Γ ,,[ A ] J) = Σ (El♭ Γ) A

↓ {Γ = emp} _ = _
↓ {Γ = (Γ ,,[ A ] J)} (x , a) = (↓ x , 𝐣 J x a)
```

---

## Bridge Types & Discrete Types {#bridge}

We define a *closed* atomic sort as a type of the form `El J (↓ x)` for some atomic sort `J : Sort Γ A` and `x : El♭ Γ`. Intuitively, a closed atomic sort of this form represents a type with the same *points* as `A x`, but that may carry additional *cohesive* or *infinitesimal* structure around these points. Given a function `b : A x → B` specifying a family of points (the *boundary*) `b a : B` for each `a : A x`, a function `f : El J (↓ x) → B` such that `f ∘ (𝐣 J x) = b` witnesses that this family of points is bound together by the same sort of cohesive/infinitesimal structure as the points of `El J (↓ x)`. We define *bridge types*  as the types of such functions:

```agda
postulate
    -- bridge types
    Bridge : ∀ {ℓ κ} {Γ : STele ℓ} {A : El♭ Γ → Set ℓ}
             → (J : Sort Γ A) (x : El♭ Γ)
             → (B : El J (↓ x) → Set κ)
             → (b : (a : A x) → B (𝐣 J x a))
             → Set (ℓ ⊔ κ)

    -- λ abstraction for bridge types
    babs : ∀ {ℓ κ} {Γ : STele ℓ} {A : El♭ Γ → Set ℓ}
           → (J : Sort Γ A) (x : El♭ Γ)
           → {B : El J (↓ x) → Set κ}
           → (f : (j : El J (↓ x)) → B j)
           → Bridge J x B (λ a → f (𝐣 J x a))
    
    -- function application for bridge types
    bapp : ∀ {ℓ κ} {Γ : STele ℓ} {A : El♭ Γ → Set ℓ}
           → (J : Sort Γ A) (x : El♭ Γ)
           → {B : El J (↓ x) → Set κ}
           → {b : (a : A x) → B (𝐣 J x a)}
           → (bb : Bridge J x B b) (j : El J (↓ x)) 
           → B j
    
    -- judgmental equalities for bridge types
    bβ : ∀ {ℓ κ} {Γ : STele ℓ} {A : El♭ Γ → Set ℓ}
         → (J : Sort Γ A) (x : El♭ Γ)
         → {B : El J (↓ x) → Set κ}
         → (f : (j : El J (↓ x)) → B j) 
         → (j : El J (↓ x))
         → bapp J x (babs J x f) j ≡ f j
    {-# REWRITE bβ #-}

    bβ𝐣 : ∀ {ℓ κ} {Γ : STele ℓ} {A : El♭ Γ → Set ℓ}
          → (J : Sort Γ A) (x : El♭ Γ)
          → {B : El J (↓ x) → Set κ}
          → {b : (a : A x) → B (𝐣 J x a)}
          → (bb : Bridge J x B b) (a : A x)
          → bapp J x bb (𝐣 J x a) ≡ b a
    {-# REWRITE bβ𝐣 #-}

    bη : ∀ {ℓ κ} {Γ : STele ℓ} {A : El♭ Γ → Set ℓ}
          → (J : Sort Γ A) (x : El♭ Γ)
          → {B : El J (↓ x) → Set κ}
          → {b : (a : A x) → B (𝐣 J x a)}
          → (bb : Bridge J x B b)
          → babs J x (λ j → bapp J x bb j) ≡ bb
    {-# REWRITE bη #-}
```

For any closed atomic sort `El J (↓ x)` with `J : Sort Γ A` and `x : El♭ Γ`, and any type `B : Set`, there is a map from paths in `B` to bridges over `El J (↓ x)` in `B` as follows:

```agda
Path→Bridge : ∀ {ℓ κ} {Γ : STele ℓ} {A : El♭ Γ → Set ℓ}
              → (J : Sort Γ A) (x : El♭ Γ)
              → {B : Set κ} {b : A x → B}
              → Σ B (λ b0 → (a : A x) → Path (λ _ → B) b0 (b a))
              → Bridge J x (λ _ → B) b
Path→Bridge J x {B = B} (b0 , p) = 
    pathJ (λ b _ → Bridge J x (λ _ → B) b) 
          (babs J x (λ _ → b0)) 
          (pabs (λ i a → papp (p a) i))
```

We say that `B` is `El J (↓ x)`-*discrete* if this map is an equivalence.

```agda
is-disc : ∀ {ℓ κ} {Γ : STele ℓ} {A : El♭ Γ → Set ℓ}
          → (J : Sort Γ A) (x : El♭ Γ) (B : Set κ)
          → Set (ℓ ⊔ κ)
is-disc {A = A} J x B = 
    {b : A x → B} → is-equiv (Path→Bridge J x {B = B} {b = b})
```

---

## The ♭ and ♭♭ Modalities {#flat}

Using Agda's modal features, we may define the ♭ modality on types as follows

```agda
data ♭ {@♭ l : Level} (@♭ A : Set l) : Set l where
  in♭ : (@♭ x : A) → ♭ A

ε : {@♭ l : Level} {@♭ A : Set l} → ♭ A → A
ε (in♭ x) = x
```

We think of types under this modality as having all bridge "flattened out", so that for any closed atomic sort `El J (↓ x)`, the only bridges definable over `El J (↓ x)` on these types are the constant ones, i.e. these types are `El J (↓ x)`-discrete. We say that types under the ♭ modality are *totally discrete*. We axiomatize this by postulating an inverse map to `Path→Bridge` for this types with judgmental equalities implying that it is both a left and a right inverse:

```agda
postulate
    -- map from bridges to paths for totally discrete types
    ♭Bridge→Path : 
        {@♭ ℓ κ : Level} {@♭ Γ : STele ℓ} {@♭ A : El♭ Γ → Set ℓ}
        → (@♭ J : Sort Γ A) (@♭ x : El♭ Γ)
        → {@♭ B : Set κ} {b : A x → ♭ B}
        → Bridge J x (λ _ → ♭ B) b
        → Σ (♭ B) (λ b0 → (a : A x) → Path (λ _ → ♭ B) b0 (b a))

    -- judgmental equalities for ♭Bridge→Path
    ♭P→B→Pconst : 
        {@♭ ℓ κ : Level} {@♭ Γ : STele ℓ} {@♭ A : El♭ Γ → Set ℓ}
        → (@♭ J : Sort Γ A) (@♭ x : El♭ Γ)
        → {@♭ B : Set κ} {b : ♭ B}
        → ♭Bridge→Path J x (babs J x (λ _ → b)) 
          ≡ (b , (λ _ → pabs (λ _ → b)))
    {-# REWRITE ♭P→B→Pconst #-}

    ♭P→B→P : 
        {@♭ ℓ κ : Level} {@♭ Γ : STele ℓ} {@♭ A : El♭ Γ → Set ℓ}
        → (@♭ J : Sort Γ A) (@♭ x : El♭ Γ)
        → {@♭ B : Set κ} {b : A x → ♭ B}
        → (b0 : ♭ B) (p : (a : A x) → Path (λ _ → ♭ B) b0 (b a))
        → ♭Bridge→Path J x (Path→Bridge J x (b0 , p)) 
          ≡ (b0 , p)
    {-# REWRITE ♭P→B→P #-}

    ♭B→P→B≡ : 
        {@♭ ℓ κ : Level} {@♭ Γ : STele ℓ} {@♭ A : El♭ Γ → Set ℓ}
        → (@♭ J : Sort Γ A) (@♭ x : El♭ Γ)
        → {@♭ B : Set κ} {b : A x → ♭ B}
        → (bb : Bridge J x (λ _ → ♭ B) b)
        → pathJ (λ b _ → Bridge J x (λ _ → ♭ B) b)
                (babs J x (λ _ → fst (♭Bridge→Path J x bb)))
                (pabs (λ i a → papp (snd (♭Bridge→Path J x bb) a) i))
          ≡ bb
    {-# REWRITE ♭B→P→B≡ #-}

-- proof that ♭ B is (El J (↓ x))-discrete for all J , x
♭disc : {@♭ ℓ κ : Level} {@♭ Γ : STele ℓ} {@♭ A : El♭ Γ → Set ℓ}
        → (@♭ J : Sort Γ A) (@♭ x : El♭ Γ) (@♭ B : Set κ)
        → is-disc J x (♭ B)
♭disc {A = A} J x B = 
    ( ( (♭Bridge→Path J x) 
      , (λ (b0 , p) → pabs (λ _ → (b0 , p)))) 
    , ( (♭Bridge→Path J x) 
      , (λ bb → pabs (λ _ → bb))) )
```

As opposed to the `♭` modality, which clobbers *all* bridge data, we would like to more selectively choose which sorts of bridges to "flatten out." For this purpose, we would like to also have modalities `♭♭ J x` for each closed atomic sort `El J (↓ x)`, where each such modality `♭♭ J x` flattens out *only* bridges defined over `El J (↓ x)`. However, at present, Agda's modal features enabled by the `--cohesion` flag include only one modality by default. However, perhaps surprisingly, having just this modality gives us a way of *defining* the universal property of the `♭♭ J x` modalities, so it follows that we can implement these modalities by postulating additional structure carrying this universal property.

Specifically, such a modality `♭♭ J x` would be a *right adjoint* to the inclusion of `El J (↓ x)`-discrete types in all types. Now, there are various *no-go theorems* (c.f. [this paper](https://arxiv.org/abs/1509.07584) §4.1) that state that the existence of such a right adjoint cannot be stated directly in the internal type-theoretic language of all types. However, it *can* be stated "externally" using the `♭` modality, as follows:

```agda
postulate
    -- the ♭♭ J x modality for each closed atomic sort El J (↓ x)
    ♭♭ : {@♭ ℓ κ : Level} {@♭ Γ : STele ℓ} {@♭ A : El♭ Γ → Set ℓ}
         → (@♭ J : Sort Γ A) (@♭ x : El♭ Γ) (@♭ B : Set κ)
         → Set κ
    
    -- map from bridges to paths for types under the ♭♭ J x modality
    -- witnessing that each such type is (El J (↓ x))-discrete
    ♭♭Bridge→Path : 
        {@♭ ℓ κ : Level} {@♭ Γ : STele ℓ} {@♭ A : El♭ Γ → Set ℓ}
        → (@♭ J : Sort Γ A) (@♭ x : El♭ Γ)
        → {@♭ B : Set κ} {b : A x → ♭♭ J x B}
        → Bridge J x (λ _ → ♭♭ J x B) b
        → Σ (♭♭ J x B) 
            (λ b0 → (a : A x) → Path (λ _ → ♭♭ J x B) b0 (b a))
    
    -- judgmental equalities for ♭♭Bridge→Path
    ♭♭P→B→Pconst : 
        {@♭ ℓ κ : Level} {@♭ Γ : STele ℓ} {@♭ A : El♭ Γ → Set ℓ}
        → (@♭ J : Sort Γ A) (@♭ x : El♭ Γ)
        → {@♭ B : Set κ} {b : ♭♭ J x B}
        → ♭♭Bridge→Path J x (babs J x (λ _ → b)) 
          ≡ (b , λ _ → pabs (λ _ → b))
    {-# REWRITE ♭♭P→B→Pconst #-}

    ♭♭P→B→P≡ : 
        {@♭ ℓ κ : Level} {@♭ Γ : STele ℓ} {@♭ A : El♭ Γ → Set ℓ}
        → (@♭ J : Sort Γ A) (@♭ x : El♭ Γ)
        → {@♭ B : Set κ} {b : A x → ♭♭ J x B}
        → (b0 : ♭♭ J x B) 
        → (p : (a : A x) → 
               Path (λ _ → ♭♭ J x B) b0 (b a))
        → ♭♭Bridge→Path J x (Path→Bridge J x (b0 , p)) ≡ (b0 , p)
    {-# REWRITE ♭♭P→B→P≡ #-}

    ♭♭B→P→B≡ : 
        {@♭ ℓ κ : Level} {@♭ Γ : STele ℓ} {@♭ A : El♭ Γ → Set ℓ}
        → (@♭ J : Sort Γ A) (@♭ x : El♭ Γ)
        → {@♭ B : Set κ} {b : A x → ♭♭ J x B}
        → (bb : Bridge J x (λ _ → ♭♭ J x B) b)
        → pathJ (λ b _ → Bridge J x (λ _ → ♭♭ J x B) b)
                (babs J x (λ _ → fst (♭♭Bridge→Path J x bb)))
                (pabs (λ i a → papp (snd (♭♭Bridge→Path J x bb) a) i))
          ≡ bb
    {-# REWRITE ♭♭B→P→B≡ #-}

-- proof that ♭♭ J x B is (El J (↓ x))-discrete
♭♭disc : {@♭ ℓ κ : Level} {@♭ Γ : STele ℓ} {@♭ A : El♭ Γ → Set ℓ}
         → (@♭ J : Sort Γ A) (@♭ x : El♭ Γ) (@♭ B : Set κ)
         → is-disc J x (♭♭ J x B)
♭♭disc J x B = 
    ( ( (♭♭Bridge→Path J x)
      , λ (b0 , p) → pabs (λ _ → (b0 , p))) 
    , ( (♭♭Bridge→Path J x) 
      , λ bb → pabs (λ _ → bb)) )

postulate
    -- counit for ♭♭ J x
    εε : {@♭ ℓ κ : Level} {@♭ Γ : STele ℓ} {@♭ A : El♭ Γ → Set ℓ}
         → (@♭ J : Sort Γ A) (@♭ x : El♭ Γ) {@♭ B : Set κ}
         → ♭♭ J x B → B

    -- constructor for ♭♭ J x
    in♭♭ : {@♭ ℓ0 ℓ1 ℓ2 : Level} {@♭ Γ : STele ℓ0} 
           → {@♭ A : El♭ Γ → Set ℓ0}
           → (@♭ J : Sort Γ A) (@♭ x : El♭ Γ) 
           → (@♭ B : Set ℓ1) (@♭ discB : is-disc J x B) 
           → {@♭ C : Set ℓ2} (@♭ f : B → C) 
           → B → ♭♭ J x C
    
    -- judgmental equalities for ♭♭ J x
    ♭♭β : {@♭ ℓ0 ℓ1 ℓ2 : Level} {@♭ Γ : STele ℓ0} 
          → {@♭ A : El♭ Γ → Set ℓ0}
          → (@♭ J : Sort Γ A) (@♭ x : El♭ Γ) 
          → (@♭ B : Set ℓ1) (@♭ discB : is-disc J x B) 
          → {@♭ C : Set ℓ2} (@♭ f : B → C) (b : B)
          → εε J x (in♭♭ J x B discB f b) ≡ f b
    {-# REWRITE ♭♭β #-}

    ♭♭η : {@♭ ℓ κ : Level} {@♭ Γ : STele ℓ} 
          → {@♭ A : El♭ Γ → Set ℓ}
          → (@♭ J : Sort Γ A) (@♭ x : El♭ Γ) 
          → {@♭ B : Set κ} (b : ♭♭ J x B)
          → in♭♭ J x (♭♭ J x B) (♭♭disc J x B) (εε J x) b ≡ b
    {-# REWRITE ♭♭η #-}
```

---

## Amazing Right Adjoints & Parametricity {#amazing}

We postulate one final characteristic property of the classifying topoi of "simple" geometric theories, as we have defined them, that serves to make the closed atomic sorts truly [atomic](https://ncatlab.org/nlab/show/tiny+object), as follows: for each closed atomic sort `El J (↓ x)`, the operation on type families `El J (↓ x) → Set` given by formation of bridge types has an [amazing right adjoint](https://ncatlab.org/nlab/show/amazing+right+adjoint). This axiom is justified by the fact that the classifying topos of every simple geometric theory is, in particular, a *presheaf topos* on a category with all finite limits, which is enough to imply that every representable presheaf (which, in our case, correspond precisely to the closed atomic sorts) gives rise to such an amazing right adjoint.

In fact, the formulation of these right adjoints we postulate is very similar to that of the ♭♭ modalities above, which we similarly postulated as certain right adjoints. As in that case, there are again certain no-go theorems (c.f. Theorem 5.1 of [this paper](https://arxiv.org/abs/1801.07664)) that forbid the possibility of axiomatizing these amazing right adjoints directly in the internal language of all types, so we get around this in exactly the same way using the `♭` modality, as in [the above-mentioned paper](https://arxiv.org/abs/1801.07664).

```agda
postulate
    -- right adjoint to formation of bridge types
    Ω : {@♭ ℓ κ : Level} {@♭ Γ : STele ℓ} {@♭ A : El♭ Γ → Set ℓ}
        → (@♭ J : Sort Γ A) (@♭ x : El♭ Γ)
        → {@♭ C : A x → Set κ} 
        → (@♭ R : ((a : A x) → C a) → Set κ)
        → (j : El J (↓ x)) → Set κ
    
    -- judgmental equality for simplifying Ω when 
    -- applied to 𝐣 J x a for some a : A x
    Ω𝐣 : {@♭ ℓ κ : Level} {@♭ Γ : STele ℓ} {@♭ A : El♭ Γ → Set ℓ}
         → (@♭ J : Sort Γ A) (@♭ x : El♭ Γ)
         → {@♭ C : A x → Set κ} 
         → (@♭ R : ((a : A x) → C a) → Set κ) (a : A x)
         → Ω J x R (𝐣 J x a) ≡ C a
    {-# REWRITE Ω𝐣 #-}
    
    -- constructor for Ω
    ω : {@♭ ℓ0 ℓ1 ℓ2 : Level} {@♭ Γ : STele ℓ0} 
        → {@♭ A : El♭ Γ → Set ℓ0}
        → (@♭ J : Sort Γ A) (@♭ x : El♭ Γ)
        → (@♭ B : El J (↓ x) → Set ℓ1) {@♭ C : A x → Set ℓ2} 
        → (@♭ R : ((a : A x) → C a) → Set ℓ2)
        → (@♭ f : (a : A x) → B (𝐣 J x a) → C a)
        → (@♭ g : {b : (a : A x) → B (𝐣 J x a)}
                  → Bridge J x B b → R (λ a → f a (b a)))
        → (j : El J (↓ x)) → B j → Ω J x R j
    
    -- simplification of ω when applied to 𝐣 J x a
    ω𝐣 : {@♭ ℓ0 ℓ1 ℓ2 : Level} {@♭ Γ : STele ℓ0} 
        → {@♭ A : El♭ Γ → Set ℓ0}
        → (@♭ J : Sort Γ A) (@♭ x : El♭ Γ)
        → (@♭ B : El J (↓ x) → Set ℓ1) {@♭ C : A x → Set ℓ2} 
        → (@♭ R : ((a : A x) → C a) → Set ℓ2)
        → (@♭ f : (a : A x) → B (𝐣 J x a) → C a)
        → (@♭ g : {b : (a : A x) → B (𝐣 J x a)} 
                  → Bridge J x B b → R (λ a → f a (b a)))
        → (a : A x) (b : B (𝐣 J x a))
        → ω J x B R f g (𝐣 J x a) b ≡ f a b
    {-# REWRITE ω𝐣 #-}
    
    -- counit of Ω
    α : {@♭ ℓ κ : Level} {@♭ Γ : STele ℓ} 
        → {@♭ A : El♭ Γ → Set ℓ}
        → (@♭ J : Sort Γ A) (@♭ x : El♭ Γ)
        → {@♭ C : A x → Set κ}
        → {@♭ R : ((a : A x) → C a) → Set κ}
        → {c : (a : A x) → C a}
        → Bridge J x (Ω J x R) c → R c

    -- judgmental equalities for Ω
    Ωβ : {@♭ ℓ0 ℓ1 ℓ2 : Level} {@♭ Γ : STele ℓ0} 
         → {@♭ A : El♭ Γ → Set ℓ0}
         → (@♭ J : Sort Γ A) (@♭ x : El♭ Γ)
         → (@♭ B : El J (↓ x) → Set ℓ1) {@♭ C : A x → Set ℓ2} 
         → (@♭ R : ((a : A x) → C a) → Set ℓ2)
         → (@♭ f : (a : A x) → B (𝐣 J x a) → C a)
         → (@♭ g : {b : (a : A x) → B (𝐣 J x a)} 
                   → Bridge J x B b → R (λ a → f a (b a)))
         → (@♭ b : (j : El J (↓ x)) → B j)
         → α J x (babs J x (λ j → ω J x B R f g j (b j))) 
           ≡ g (babs J x b)
    {-# REWRITE Ωβ #-}

    Ωη : {@♭ ℓ κ : Level} {@♭ Γ : STele ℓ} 
         → {@♭ A : El♭ Γ → Set ℓ}
         → (@♭ J : Sort Γ A) (@♭ x : El♭ Γ)
         → {@♭ C : A x → Set κ}
         → {@♭ R : ((a : A x) → C a) → Set κ}
         → (j : El J (↓ x)) (w : Ω J x R j)
         → ω J x (Ω J x R) R (λ _ c → c) (α J x) j w ≡ w
    {-# REWRITE Ωη #-}
```

The constructor `ω` for `Ω` is rather complex and so can be unwieldy to use directly. We therefore define the following special case of ω for streamlining simpler constructions involving Ω.

```agda
-- instances of ω where domain type is unit
ω1 : {@♭ ℓ κ : Level} {@♭ Γ : STele ℓ} 
     → {@♭ A : El♭ Γ → Set ℓ}
     → (@♭ J : Sort Γ A) (@♭ x : El♭ Γ)
     → {@♭ C : A x → Set κ} 
     → (@♭ R : ((a : A x) → C a) → Set κ)
     → (@♭ c : (a : A x) → C a) (@♭ r : R c)
     → (j : El J (↓ x)) → Ω J x R j
ω1 J x R c r j = 
    ω {ℓ1 = lzero} J x (λ _ → ⊤) R 
      (λ a _ → c a) (λ _ → r) j _
```

Additionally, we define the following witness to the functoriality of Ω:

```agda
-- functoriality of Ω
Ωfunctor : 
    {@♭ ℓ0 ℓ1 ℓ2 : Level} {@♭ Γ : STele ℓ0} 
    → {@♭ A : El♭ Γ → Set ℓ0}
    → (@♭ J : Sort Γ A) (@♭ x : El♭ Γ)
    → {@♭ B : A x → Set ℓ1} 
    → (@♭ RB : ((a : A x) → B a) → Set ℓ1)
    → {@♭ C : A x → Set ℓ2} 
    → (@♭ RC : ((a : A x) → C a) → Set ℓ2)
    → (@♭ f : (a : A x) → B a → C a)
    → (@♭ g : {b : (a : A x) → B a} 
              → RB b → RC (λ a → f a (b a)))
    → (j : El J (↓ x)) → Ω J x RB j → Ω J x RC j
Ωfunctor J x RB RC f g j w = 
    ω J x (Ω J x RB) RC f 
      (λ u → g (α J x u)) j w
```

A notable consequence of our assumption of amazing right adjoints for each closed atomic sort is that it enables us to prove various *parametricity* theorems internally in Agda. For instance, a proof of the (unary) parametricity theorem for the type `(X : Set) → X → X` of the polymorphic identity function is as follows:

```agda
-- unary parametricity for the type of the polymorphic
-- identity function, assuming a closed atomic sort
-- with one constant
module paramId (@♭ J : Sort {ℓ = lzero} emp (λ _ → ⊤))
               (Ϝ : (X : Set₀) → X → X)
               (@♭ A : Set₀) (@♭ B : A → Set₀)
               (@♭ a : A) (@♭ b : B a)
               where

    param : B (Ϝ A a)
    param = α J _ (babs J _ (λ j → 
              Ϝ (Ω J _ (λ f → B (f _)) j) 
                (ω1 J _ _ (λ _ → a) b j)))
```

This proof straightforwardly generalizes to arbitrary arities of parametricity by replacing `J` in the above with a `K`-pointed atomic sort.

Moreover, this form of parametricity extends (at least) to the types of impredicative encodings of inductive types and indeed *higher* inductive types. As an example, we demonstrate this for the cases of the impredicative encodings of the natural numbers and the circle, respectively:

```agda
-- parametricity for impredicative encoding of 
-- natural numbers
module paramNat 
         (@♭ J : Sort {ℓ = lzero} emp (λ _ → ⊤))
         (Ϝ : (X : Set₀) → X → (X → X) → X)
         (@♭ A : Set₀) (@♭ B : A → Set₀)
         (@♭ a : A) (@♭ b : B a)
         (@♭ f : A → A) (@♭ g : {a : A} → B a → B (f a))
         where

    param : B (Ϝ A a f)
    param = 
        α J _ (babs J _ (λ j → 
          Ϝ (Ω J _ (λ h → B (h _)) j) 
            (ω1 J _ _ (λ _ → a) b j)
            (Ωfunctor J _ _ _ (λ _ → f) (λ x → g x) j)))
```

```agda
-- parametricity for impredicative encoding of S1
module paramS1 
         (@♭ J : Sort {ℓ = lzero} emp (λ _ → ⊤))
         (Ϝ : (X : Set₀) (x y : X) → Path (λ _ → X) x y → X)
         (@♭ A : Set₀) (@♭ B : A → Set₀)
         (@♭ a0 a1 : A) (@♭ b0 : B a0) (@♭ b1 : B a1)
         (@♭ p : Path (λ _ → A) a0 a1)
         (@♭ q : Path (λ i → B (papp p i)) b0 b1)
         where
    
    param : B (Ϝ A a0 a1 p)
    param = α J _ (babs J _ (λ j → 
            Ϝ (Ω J _ (λ f → B (f _)) j) 
              (lemma j i0) (lemma j i1) 
              (pabs (λ i → lemma j i))))
      where lemma : (j : El J (↓ _)) (i : I)
                    → Ω J _ (λ f → B (f _)) j
            lemma = ω J _ (λ _ → I) _ (λ _ → papp p) 
                      (λ b → papp q (bapp J _ b (𝐣 J _ _)))
```

---

## Instances of Impredicativity {#impred}

The fact that Synthetic Agda is capable of proving such parametricity theorems as above *internally* makes it an ideal playground for experimenting with [impredicative encodings](https://arxiv.org/abs/1802.02820) of constructs defined by universal properties, such inductive types, higher inductive types, coinductive types, adjoint functors, etc. Unrestricted impredicativity, however, would be a very strong assumption (e.g. it is anti-classical), so we do not make this assumption directly. Instead, we let the user postulate their own *instances of impredicativity*, by way of axioms that create isomorphic instances of types in universes at lower levels than would normally exist under Agda's predicative hierarchy of universes.

We define an instance of impredicativity as a type of level-polymorphic functions `∀ {ℓ} (x : X ℓ) → Y ℓ x` where `X : (ℓ : Level) → Set (L ℓ)` for some `L : Level → Level` and `Y : (ℓ : Level) → X ℓ → Set (K ℓ)` for some `K : Level → Level`. We thus postulate a type `Impred X Y` for each such X , Y pair, such that an element `x : Impred X Y` allows us to construct an isomorphic copy of `∀ {ℓ} (x : X ℓ) → Y ℓ x` at level `K (lzero)`.

```agda
postulate
    -- instances of impredicativity
    Impred : {L K : Level → Level} 
             → (X : (ℓ : Level) → Set (L ℓ))
             → (Y : (ℓ : Level) → X ℓ → Set (K ℓ))
             → Setω

    -- impredicative Π types
    Π! : {L K : Level → Level}
         → (X : (ℓ : Level) → Set (L ℓ))
         → (Y : (ℓ : Level) → X ℓ → Set (K ℓ))
         → Impred X Y
         → Set (K lzero)
    
    -- λ abstraction for impredicative Π types
    Λ! : {L K : Level → Level}
         → {X : (ℓ : Level) → Set (L ℓ)}
         → {Y : (ℓ : Level) → X ℓ → Set (K ℓ)}
         → (u : Impred X Y)
         → (f : ∀ {ℓ} (x : X ℓ) → Y ℓ x)
         → Π! X Y u
    
    -- function application for impredicative Π types
    app! : {L K : Level → Level}
           → {X : (ℓ : Level) → Set (L ℓ)}
           → {Y : (ℓ : Level) → X ℓ → Set (K ℓ)}
           → (u : Impred X Y)
           → (Ϝ : Π! X Y u) {ℓ : Level} (x : X ℓ)
           → Y ℓ x
    
    -- judgmental equalities for impredicative Π types
    Π!β : {L K : Level → Level}
          → {X : (ℓ : Level) → Set (L ℓ)}
          → {Y : (ℓ : Level) → X ℓ → Set (K ℓ)}
          → (u : Impred X Y)
          → (f : ∀ {ℓ} (x : X ℓ) → Y ℓ x)
          → {ℓ : Level} (x : X ℓ)
          → app! u (Λ! u f) x ≡ f x
    {-# REWRITE Π!β #-}

    Π!η : {L K : Level → Level}
          → {X : (ℓ : Level) → Set (L ℓ)}
          → {Y : (ℓ : Level) → X ℓ → Set (K ℓ)}
          → (u : Impred X Y)
          → (Ϝ : Π! X Y u)
          → Λ! u (λ x → app! u Ϝ x) ≡ Ϝ
    {-# REWRITE Π!η #-}
```

---

# Conclusion – Toward the Type Theory of Topoi {#conclusion}

The above constitutes the main axiomatic and computational framework of Synthetic Agda. As it stands, this framework is very much a work-in-progress, and it is altogether certain that these axioms will be subject to continued reformulations, modifications, and extensions as experience working with this framework demonstrates its shortcomings or unrealized possibilities. In this spirit, we conclude with a brief assessment of the prospects for Synthetic Agda and its continued development.

Coming back to our original motivation of studying the internal type-theoretic languages of arbitrary (∞-)Grothendieck topoi, one significant piece remains yet unaccounted for. Although we have given a robust axiomatization of the internal languages of the classifying topoi of *simple* geometric theories, i.e. theories without axioms, we have not yet said anything about the classifying topoi of general theories with axioms.

Any geometric theory is a quotient of the underlying simple theory given by its signature – hence every (∞-)Grothendieck topos is a subtopos (i.e. a reflective subcategory whose reflector preserves finite limits) of the classifying (∞-)topos of a simple theory. Hence provided our axiomatization of the internal languages of these latter classifying topoi is expressive enough, we should be able to isolate the former topoi as [reflective localizations](https://ncatlab.org/nlab/show/reflective+localization) of types in this framework. More work is certainly needed to make this idea precise and see if it holds water, but at the very least having a working computational framework in which to experiment with such possibilities offers a promising first step in this direction.

If you have questions, comments, or are interested in contributing to the development of Synthetic Agda and/or synthetic mathematics using Synthetic Agda, please do get in touch! 

* [Email](mailto:caberle@andrew.cmu.edu)
* [Mathstodon](https://mathstodon.xyz/@cbaberle)