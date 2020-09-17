{-# OPTIONS --without-K --safe #-}

open import Level using (Level)
open import FLA.Algebra.Structures
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

module FLA.Algebra.Properties.Field {ℓ : Level } {A : Set ℓ} ⦃ F : Field A ⦄ where

open Field F

0ᶠ+0ᶠ≡0ᶠ : 0ᶠ + 0ᶠ ≡ 0ᶠ
0ᶠ+0ᶠ≡0ᶠ = +-0 0ᶠ

0-+ : (a : A) → 0ᶠ + a ≡ a
0-+ a rewrite +-comm 0ᶠ a = +-0 a
