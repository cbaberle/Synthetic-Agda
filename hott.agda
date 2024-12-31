{-# OPTIONS --without-K --rewriting --cubical-compatible #-}
module hott where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma

-- unit type
record ⊤ {ℓ} : Set ℓ where
    constructor tt

-- binary products
_×_ : ∀ {ℓ κ} (A : Set ℓ) (B : Set κ) → Set (ℓ ⊔ κ)
A × B = Σ A (λ _ → B)

postulate
    -- the interval
    I : Set₀

    -- endpoints of the interval
    i0 i1 : I

    -- path types
    Path : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1 → Set ℓ

    -- function abstraction for path types
    pabs : ∀ {ℓ} {A : I → Set ℓ}
           → (f : (i : I) → A i)
           → Path A (f i0) (f i1)
    
    -- function application for path types
    papp : ∀ {ℓ} {A : I → Set ℓ} {a0 : A i0} {a1 : A i1}
           → Path A a0 a1 → (i : I) → A i
    
    -- judgmental equalities for path types
    pathβ : ∀ {ℓ} {A : I → Set ℓ}
            → (f : (i : I) → A i) (i : I)
            → papp (pabs f) i ≡ f i
    {-# REWRITE pathβ #-}
    
    pathβ0 :  ∀ {ℓ} {A : I → Set ℓ} 
              → {a0 : A i0} {a1 : A i1}
              → (p : Path A a0 a1)
              → papp p i0 ≡ a0
    {-# REWRITE pathβ0 #-}

    pathβ1 :  ∀ {ℓ} {A : I → Set ℓ} 
              → {a0 : A i0} {a1 : A i1}
              → (p : Path A a0 a1)
              → papp p i1 ≡ a1
    {-# REWRITE pathβ1 #-}

    pathη :  ∀ {ℓ} {A : I → Set ℓ} 
             → {a0 : A i0} {a1 : A i1}
             → (p : Path A a0 a1)
             → pabs (λ i → papp p i) ≡ p
    {-# REWRITE pathη #-}

    -- path induction
    pathJ : ∀ {ℓ κ} {A : Set ℓ} {a0 a1 : A}
            → (B : (a' : A) → Path (λ _ → A) a0 a' → Set κ)
            → (r : B a0 (pabs (λ _ → a0)))
            → (p : Path (λ _ → A) a0 a1)
            → B a1 p
    
    -- β law for path induction
    pathJβ : ∀ {ℓ κ} {A : Set ℓ} {a : A}
            → (B : (a' : A) → Path (λ _ → A) a a' → Set κ)
            → (b : B a (pabs (λ _ → a)))
            → pathJ B b (pabs (λ _ → a)) ≡ b
    {-# REWRITE pathJβ #-}

-- definition of equivalence in terms of bi-invertible maps
is-equiv : ∀ {ℓ κ} {A : Set ℓ} {B : Set κ} (f : A → B) → Set (ℓ ⊔ κ)
is-equiv {A = A} {B = B} f =
      (Σ (B → A) (λ g → (x : A) → Path (λ _ → A) (g (f x)) x))
    × (Σ (B → A) (λ h → (y : B) → Path (λ _ → B) (f (h y)) y))