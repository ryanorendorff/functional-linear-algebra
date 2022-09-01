{-# OPTIONS --without-K --safe #-}

open import Level using (Level)
open import FLA.Algebra.Structures
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module FLA.Algebra.Properties.Field {ℓ : Level } {A : Set ℓ} ⦃ F : Field A ⦄ where

open Field F

-- Convenience reordering of existing proofs so that other proofs can be
-- shorter/more readible.

0ᶠ+ : (a : A) → 0ᶠ + a ≡ a
0ᶠ+ a = trans (+-comm 0ᶠ a) (+0ᶠ a)

1ᶠ* : (a : A) → 1ᶠ * a ≡ a
1ᶠ* a = trans (*-comm 1ᶠ a) (*1ᶠ a)

*-distrᵣ-+ : (a b c : A) → a * (b + c) ≡ b * a + c * a
*-distrᵣ-+ a b c = trans (*-distr-+ a b c) (cong₂ _+_ (*-comm a b) (*-comm a c))

-- Proofs for common operations derived from the base axioms but not included in
-- them.

0ᶠ+0ᶠ≡0ᶠ : 0ᶠ + 0ᶠ ≡ 0ᶠ
0ᶠ+0ᶠ≡0ᶠ = +0ᶠ 0ᶠ

a*0ᶠ≡0ᶠ : (a : A) → a * 0ᶠ ≡ 0ᶠ
a*0ᶠ≡0ᶠ a = begin
  a * 0ᶠ                  ≡˘⟨ 0ᶠ+ (a * 0ᶠ) ⟩
  0ᶠ + a * 0ᶠ             ≡⟨ cong (_+ a * 0ᶠ) (sym (+-inv a)) ⟩
  - a + a + a * 0ᶠ        ≡⟨ cong (λ x → - a + x + a * 0ᶠ) (sym (*1ᶠ a)) ⟩
  - a + a * 1ᶠ + a * 0ᶠ   ≡˘⟨ +-assoc (- a) (a * 1ᶠ) (a * 0ᶠ) ⟩
  - a + (a * 1ᶠ + a * 0ᶠ) ≡⟨ cong (- a +_) (sym (*-distr-+ a 1ᶠ 0ᶠ)) ⟩
  - a + (a * (1ᶠ + 0ᶠ))   ≡⟨ cong (λ x → - a + (a * x)) (+0ᶠ 1ᶠ) ⟩
  - a + (a * 1ᶠ)          ≡⟨ cong (- a +_) (*1ᶠ a) ⟩
  - a + a                 ≡⟨ +-inv a ⟩
  0ᶠ                      ∎

0ᶠ*a≡0ᶠ : (a : A) → 0ᶠ * a ≡ 0ᶠ
0ᶠ*a≡0ᶠ a = trans (*-comm 0ᶠ a) (a*0ᶠ≡0ᶠ a)

-a≡-1ᶠ*a : (a : A) → - a ≡ - 1ᶠ * a
-a≡-1ᶠ*a a = begin
  - a                        ≡˘⟨ +0ᶠ (- a) ⟩
  - a + 0ᶠ                   ≡⟨ cong (- a +_) (sym (a*0ᶠ≡0ᶠ a)) ⟩
  - a + (a * 0ᶠ)             ≡⟨ cong (λ x → - a + (a * x)) (sym (+-inv 1ᶠ)) ⟩
  - a + (a * (- 1ᶠ + 1ᶠ))    ≡⟨ cong (- a +_) (*-distr-+ a (- 1ᶠ) 1ᶠ) ⟩
  - a + (a * - 1ᶠ + a * 1ᶠ)  ≡⟨ cong (- a +_) (+-comm (a * - 1ᶠ) (a * 1ᶠ)) ⟩
  - a + (a * 1ᶠ + a * - 1ᶠ ) ≡⟨ +-assoc (- a) (a * 1ᶠ) (a * - 1ᶠ) ⟩
  - a + a * 1ᶠ + a * - 1ᶠ    ≡⟨ cong (λ x → - a + x + a * - 1ᶠ) (*1ᶠ a) ⟩
  - a + a + a * - 1ᶠ         ≡⟨ cong (_+ a * - 1ᶠ) (+-inv a) ⟩
  0ᶠ + a * - 1ᶠ              ≡⟨ 0ᶠ+ (a * - 1ᶠ) ⟩
  a * - 1ᶠ                   ≡⟨ *-comm a (- 1ᶠ) ⟩
  - 1ᶠ * a                   ∎

-a*b≡-[a*b] : (a b : A) → - a * b ≡ - (a * b)
-a*b≡-[a*b] a b = begin
  - a * b        ≡⟨ cong (_* b) (-a≡-1ᶠ*a a) ⟩
  (- 1ᶠ * a) * b ≡˘⟨ *-assoc (- 1ᶠ) a b ⟩
  - 1ᶠ * (a * b) ≡˘⟨ -a≡-1ᶠ*a ((a * b)) ⟩
  - (a * b)      ∎

a*-b≡-[a*b] : (a b : A) → a * - b ≡ - (a * b)
a*-b≡-[a*b] a b = begin
  a * - b   ≡⟨ *-comm a (- b) ⟩
  - b * a   ≡⟨ -a*b≡-[a*b] b a ⟩
  - (b * a) ≡⟨ cong -_ (*-comm b a) ⟩
  - (a * b) ∎

-[a+b]≡-a+-b : (a b : A) → - (a + b) ≡ - a + - b
-[a+b]≡-a+-b a b = begin
  - (a + b)           ≡⟨ -a≡-1ᶠ*a (a + b) ⟩
  - 1ᶠ * (a + b)      ≡⟨ *-distr-+ (- 1ᶠ) a b ⟩
  - 1ᶠ * a + - 1ᶠ * b ≡⟨ cong₂ _+_ (sym (-a≡-1ᶠ*a a)) (sym (-a≡-1ᶠ*a b)) ⟩
  - a + - b           ∎

-- Sometimes called the law of signs
-a*-b≡a*b  : (a b : A) → - a * - b ≡ a * b
-a*-b≡a*b a b = begin
  - a * - b                     ≡˘⟨ +0ᶠ (- a * - b) ⟩
  - a * - b + 0ᶠ                ≡⟨ cong (- a * - b +_) (sym (a*0ᶠ≡0ᶠ a)) ⟩
  - a * - b + a * 0ᶠ            ≡⟨ cong (λ p → - a * - b + a * p)
                                        (sym (+-inv b)) ⟩
  - a * - b + a * (- b + b)     ≡⟨ cong (- a * - b +_) (*-distr-+ a (- b) b) ⟩
  - a * - b + (a * - b + a * b) ≡⟨ +-assoc (- a * - b) (a * - b) (a * b) ⟩
  - a * - b + a * - b + a * b   ≡⟨ cong₂ (λ p q → p + q + a * b)
                                         (*-comm (- a) (- b)) (*-comm a (- b)) ⟩
  - b * - a + - b * a + a * b   ≡⟨ cong (_+ a * b)
                                        (sym (*-distr-+ (- b) (- a) a)) ⟩
  - b * (- a + a) + a * b       ≡⟨ cong (λ p → - b * p + a * b) (+-inv a) ⟩
  - b * 0ᶠ + a * b              ≡⟨ cong (_+ a * b) (a*0ᶠ≡0ᶠ (- b)) ⟩
  0ᶠ + a * b                    ≡⟨ 0ᶠ+ (a * b) ⟩
  a * b                         ∎

-[-a]≡a : (a : A) → - (- a) ≡ a
-[-a]≡a a = begin
  - (- a)           ≡⟨ -a≡-1ᶠ*a (- a) ⟩
  - 1ᶠ * (- a)      ≡⟨ cong (- 1ᶠ *_) (-a≡-1ᶠ*a a) ⟩
  - 1ᶠ * (- 1ᶠ * a) ≡⟨ *-assoc (- 1ᶠ) (- 1ᶠ) a ⟩
  - 1ᶠ * - 1ᶠ * a   ≡⟨ cong (_* a) (-a*-b≡a*b 1ᶠ 1ᶠ) ⟩
  1ᶠ * 1ᶠ * a       ≡⟨ cong (_* a) (*1ᶠ 1ᶠ) ⟩
  1ᶠ * a            ≡⟨ trans (*-comm 1ᶠ a) (*1ᶠ a) ⟩
  a                 ∎
