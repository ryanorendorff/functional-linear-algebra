{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

open import Relation.Binary.PropositionalEquality hiding (∀-extensionality)
open ≡-Reasoning

open import Data.Nat using (ℕ; suc; zero)
open import Data.Vec using (Vec; foldr; zipWith; map)

open import FLA.Algebra.Structures
open import FLA.Algebra.Properties.Field

module FLA.Algebra.LinearAlgebra where

private
  variable
    ℓ : Level
    A : Set ℓ
    m n p q : ℕ


module _ {ℓ : Level} {A : Set ℓ} ⦃ F : Field A ⦄ where
  open Field F

  -- Vector addition
  _+ⱽ_ : ⦃ F : Field A ⦄ → Vec A n → Vec A n → Vec A n
  _+ⱽ_ = zipWith _+_

  -- Vector Hadamard product
  _∘ⱽ_ : ⦃ F : Field A ⦄ → Vec A n → Vec A n → Vec A n
  _∘ⱽ_ = zipWith _*_

  -- Multiply vector by a constant
  _*ᶜ_ : ⦃ F : Field A ⦄ → A → Vec A n → Vec A n
  c *ᶜ v = map (c *_) v

  -- Match the fixity of Haskell
  infixl  6 _+ⱽ_
  infixl  7 _∘ⱽ_
  infixl 10 _*ᶜ_

  sum : Vec A n → A
  sum = foldr _ _+_ 0ᶠ

-- Inner product
⟨_,_⟩ : ⦃ F : Field A ⦄ → Vec A n → Vec A n → A
⟨ v₁ , v₂ ⟩ = sum (v₁ ∘ⱽ v₂)
