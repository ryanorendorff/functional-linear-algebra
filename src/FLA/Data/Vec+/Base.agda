{-# OPTIONS --without-K --safe #-}

open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Empty using (⊥)
open import Data.Vec using (Vec)
                     renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)

module FLA.Data.Vec+.Base where

private
  variable
    ℓ : Level
    A : Set ℓ
    n : ℕ

-- TODO: Can this be replaced with something like the List⁺ definition so that
-- the proofs from Vec can be transferred? This definition is convenient because
-- the size is correct (it is not n - 1).
data Vec⁺ (A : Set ℓ) : ℕ → Set ℓ where
  [_] : A → Vec⁺ A 1
  _∷_ : ∀ {n} (x : A) (xs : Vec⁺ A n) → Vec⁺ A (suc n)

infixr 5 _∷_

-- Want to prove that is it not possible to construct an empty vector
emptyVecImpossible : Vec⁺ A 0 → ⊥
emptyVecImpossible = λ ()

Vec⁺→Vec : Vec⁺ A n → Vec A n
Vec⁺→Vec [ v ] = v ∷ⱽ []ⱽ
Vec⁺→Vec (v ∷ vs⁺) = v ∷ⱽ Vec⁺→Vec vs⁺

Vec⁺→n≢0 : Vec⁺ A n → n ≢ 0
Vec⁺→n≢0 {ℓ} {A} {suc n} v = suc≢0
  where
    suc≢0 : {n : ℕ} → suc n ≢ 0
    suc≢0 {zero} ()
    suc≢0 {suc n} = λ ()

-- Closer maybe but still buggered
-- Vec→Vec⁺ : ∀ {ℓ} → {A : Set ℓ} {n : ℕ} → (n ≢ 0) → Vec A n → Vec⁺ A n
-- Vec→Vec⁺ {ℓ} {A} {0} p []ⱽ = ⊥-elim (p refl)
-- Vec→Vec⁺ {ℓ} {A} {1} p (x ∷ⱽ []ⱽ) = [ x ]
-- Vec→Vec⁺ {ℓ} {A} {suc n} p (x ∷ⱽ xs) = x ∷ (Vec→Vec⁺ {!!} xs)
