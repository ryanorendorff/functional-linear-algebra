{-# OPTIONS --without-K --safe #-}

open import Level using (Level)
open import FLA.Algebra.Structures
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module FLA.Algebra.Properties.Field {ℓ : Level } {A : Set ℓ} ⦃ F : Field A ⦄ where

open Field F

0ᶠ+0ᶠ≡0ᶠ : 0ᶠ + 0ᶠ ≡ 0ᶠ
0ᶠ+0ᶠ≡0ᶠ = +0ᶠ 0ᶠ

0ᶠ+ : (a : A) → 0ᶠ + a ≡ a
0ᶠ+ a rewrite +-comm 0ᶠ a = +0ᶠ a


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
