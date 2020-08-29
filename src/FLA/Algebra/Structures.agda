{-# OPTIONS --without-K --safe #-}

-- We do not parameterize this module since we do not have access to _+_ or _*_
-- for the fields that we want (real numbers)

module FLA.Algebra.Structures where

open import Level using (Level) renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

private
  variable
    ℓ : Level
    A : Set ℓ

record Field (A : Set ℓ) : Set ℓ where

  infixl 6 _+_
  infixl 7 _*_
  infixl 9 -_
  infixl 10 _⁻¹

  field
    _+_ : A → A → A
    _*_ : A → A → A

    0ᶠ   : A
    1ᶠ   : A
    -_   : A → A -- + inverse
    _⁻¹  : A → A -- * inverse

    +-assoc   : (a b c : A) → a + (b + c) ≡ (a + b) + c
    +-comm    : (a b : A)   → a + b ≡ b + a
    +-0       : (a : A)     → a + 0ᶠ ≡ a
    +-inv     : (a : A)     → - a + a ≡ 0ᶠ
    *-assoc   : (a b c : A) → a * (b * c) ≡ (a * b) * c
    *-comm    : (a b : A)   → a * b ≡ b * a
    *-1       : (a : A)     → a * 1ᶠ ≡ a
    *-inv     : (a : A)     → (a ≢ 0ᶠ) → a ⁻¹ * a ≡ 1ᶠ
    *-distr-+ : (a b c : A) → a * (b + c) ≡ a * b + a * c


record LinearlyOrdered (A : Set ℓ) : Set (lsuc ℓ) where

  infixl 5 _≤_

  field
    _≤_ : A → A → Set ℓ

    -- TODO: find the standard library way to represent a sum
    -- total : x ≤ y or y ≤ x
    trans : (x y z : A) → x ≤ y → y ≤ z → x ≤ z
    anti-sym : (x y : A) → x ≤ y → y ≤ x → x ≡ y


-- record LinearlyOrderedField (A : Set ℓ) : Set ℓ where
--   open Field
--   open LinearlyOrdered

--   field
--     x≤y→z+x≤z+y : (x y z : A) → x ≤ y → z + x ≤ z + y
--     0≤x→0≤y→0≤x*y : (x y : A) → 0 ≤ x → 0 ≤ y → 0 ≤ x * y

-- record CompleteOrderedField (A : Set ℓ) : Set ℓ where
--   open LinearlyOrderedField

--   -- Proof of the supremum rule

{-
If we want the reals, we need a few things

Linearly ordered set on F, ∀ x, y, z ∈ F
  Totality : x ≤ y or y ≤ x
  Transitivity : if x ≤ y and y ≤ z then x ≤ z
  Anti-symmetry : if x ≤ y and y ≤ x, then x ≡ y

Linearly ordered field (F, +, *, ≤) if
  x ≤ y then z + x ≤ z + y
  0 ≤ x and 0 ≤ y then 0 ≤ x*y

Complete ordered field (F, +, *, ≤) if
  (F, +, *, ≤) is a linearly ordered field
  Completeness : every non-empty subset of F, bounded above, has a supremum in F

Archimedian property:
  (F, +, *, ≤) is a complete ordered field
  r, s ∈ F. r > 0 ∃ n ∈ ℕ. s < r + ... + r (n times)

  Roughly speaking, it is the property of having no infinitely large or
  infinitely small elements

  Axiom of Archimedies is a formulation of this property for ordered fields:
    ∀ ε ∈ F. ε > 0 → ∃ n ∈ ℕ . 1/n < ε

Cauchy sequences representation of the reals and the Dedekind representation
of the reals are both Archimedian completely ordered fields and hence
isomorphic to the reals. Note there is a proof that all Archimedian complete
ordered fields are isomorphic.

References:
[1]: https://www.cs.swan.ac.uk/~csetzer/articlesFromOthers/chiMing/chiMingChuangExtractionOfProgramsForExactRealNumberComputation.pdf
[2]: https://en.wikipedia.org/wiki/Axiomatic_theory_of_real_numbers
-}
