{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

open import Relation.Binary.PropositionalEquality hiding (∀-extensionality)
open ≡-Reasoning

open import Data.Nat using (ℕ; suc; zero)
open import Data.Vec using (Vec; foldr; zipWith; map)
                     renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)

open import FLA.Algebra.Structures
open import FLA.Algebra.Properties.Field
open import FLA.Algebra.LinearAlgebra

module FLA.Algebra.LinearAlgebra.Properties where

private
  variable
    ℓ : Level
    A : Set ℓ
    m n p q : ℕ
    ⦃ F ⦄ : Field A

zipWith-comm : (f : A → A → A) → (f-comm : (a b : A) → f a b ≡ f b a)
             → (x y : Vec A n) → zipWith f x y ≡ zipWith f y x
zipWith-comm f f-comm []ⱽ []ⱽ = refl
zipWith-comm f f-comm (x ∷ⱽ xs) (y ∷ⱽ ys) rewrite
    zipWith-comm f f-comm xs ys
  | f-comm x y = refl

+ⱽ-assoc : ⦃ F : Field A ⦄ → (v₁ v₂ v₃ : Vec A n)
         → v₁ +ⱽ v₂ +ⱽ v₃ ≡ v₁ +ⱽ (v₂ +ⱽ v₃)
+ⱽ-assoc []ⱽ []ⱽ []ⱽ = refl
+ⱽ-assoc ⦃ F ⦄ (v₁ ∷ⱽ vs₁) (v₂ ∷ⱽ vs₂) (v₃ ∷ⱽ vs₃) rewrite
    +ⱽ-assoc vs₁ vs₂ vs₃
  | Field.+-assoc F v₁ v₂ v₃
    = refl

+ⱽ-comm : ⦃ F : Field A ⦄ → (v₁ v₂ : Vec A n) → v₁ +ⱽ v₂ ≡ v₂ +ⱽ v₁
+ⱽ-comm []ⱽ []ⱽ = refl
+ⱽ-comm (x₁ ∷ⱽ vs₁) (x₂ ∷ⱽ vs₂) = begin
  x₁ + x₂ ∷ⱽ vs₁ +ⱽ vs₂
  ≡⟨ cong ((x₁ + x₂) ∷ⱽ_) (+ⱽ-comm vs₁ vs₂) ⟩
  x₁ + x₂ ∷ⱽ vs₂ +ⱽ vs₁
  ≡⟨ cong (_∷ⱽ vs₂ +ⱽ vs₁) (+-comm x₁ x₂) ⟩
  x₂ + x₁ ∷ⱽ vs₂ +ⱽ vs₁
  ∎
  where open Field {{...}}

∘ⱽ-comm : ⦃ F : Field A ⦄ → (v₁ v₂ : Vec A n) → v₁ ∘ⱽ v₂ ≡ v₂ ∘ⱽ v₁
∘ⱽ-comm []ⱽ []ⱽ = refl
∘ⱽ-comm ⦃ F ⦄ (v₁ ∷ⱽ vs₁) (v₂ ∷ⱽ vs₂) rewrite
    ∘ⱽ-comm vs₁ vs₂
  | Field.*-comm F v₁ v₂
  = refl

∘ⱽ-distr-+ⱽ : ⦃ F : Field A ⦄ → (a u v : Vec A n)
            → a ∘ⱽ (u +ⱽ v) ≡ a ∘ⱽ u +ⱽ a ∘ⱽ v
∘ⱽ-distr-+ⱽ []ⱽ []ⱽ []ⱽ = refl
∘ⱽ-distr-+ⱽ ⦃ F ⦄ (a ∷ⱽ as) (u ∷ⱽ us) (v ∷ⱽ vs) rewrite
    ∘ⱽ-distr-+ⱽ as us vs
  | Field.*-distr-+ F a u v
  = refl

-- Homogeneity of degree 1 for linear maps
∘ⱽ*ᶜ≡*ᶜ∘ⱽ : ⦃ F : Field A ⦄ → (c : A) (u v : Vec A n)
          → u ∘ⱽ c *ᶜ v ≡ c *ᶜ (u ∘ⱽ v)
∘ⱽ*ᶜ≡*ᶜ∘ⱽ c []ⱽ []ⱽ = refl
∘ⱽ*ᶜ≡*ᶜ∘ⱽ ⦃ F ⦄ c (u ∷ⱽ us) (v ∷ⱽ vs) rewrite
    ∘ⱽ*ᶜ≡*ᶜ∘ⱽ c us vs
  | Field.*-assoc F u c v
  | Field.*-comm F u c
  | sym (Field.*-assoc F c u v)
  = refl

*ᶜ-distr-+ⱽ : ⦃ F : Field A ⦄
            → (c : A) (u v : Vec A n)
            → c *ᶜ (u +ⱽ v) ≡ c *ᶜ u +ⱽ c *ᶜ v
*ᶜ-distr-+ⱽ c []ⱽ []ⱽ = refl
*ᶜ-distr-+ⱽ ⦃ F ⦄ c (u ∷ⱽ us) (v ∷ⱽ vs) rewrite
    *ᶜ-distr-+ⱽ c us vs
  | Field.*-distr-+ F c u v
  = refl

⟨⟩-comm : ⦃ F : Field A ⦄ → (v₁ v₂ : Vec A n)
        → ⟨ v₁ , v₂ ⟩ ≡ ⟨ v₂ , v₁ ⟩
⟨⟩-comm []ⱽ []ⱽ = refl
⟨⟩-comm ⦃ F ⦄ (x₁ ∷ⱽ v₁) (x₂ ∷ⱽ v₂) rewrite
    ⟨⟩-comm v₁ v₂
  | Field.*-comm F x₁ x₂
  = refl


-- Should we show bilinearity?
--   ∀ λ ∈ F, B(λv, w) ≡ B(v, λw) ≡ λB(v, w)
--   B(v₁ + v₂, w) ≡ B(v₁, w) + B(v₂, w) ∧ B(v, w₁ + w₂) ≡ B(v, w₁) + B(v, w₂)
-- Additivity in both arguments
private
  module ⟨⟩-Properties ⦃ F : Field A ⦄ where
    open Field F

    ⟨x+y,z⟩≡⟨x,z⟩+⟨y,z⟩ : (x y z : Vec A n)
                        → ⟨ x +ⱽ y , z ⟩ ≡ (⟨ x , z ⟩) + (⟨ y , z ⟩)
    ⟨x+y,z⟩≡⟨x,z⟩+⟨y,z⟩ x y z = begin
      ⟨ x +ⱽ y , z ⟩
      ≡⟨⟩
      sum ((x +ⱽ y) ∘ⱽ z )
      ≡⟨ cong sum (∘ⱽ-comm (x +ⱽ y) z) ⟩
      sum (z ∘ⱽ (x +ⱽ y))
      ≡⟨ cong sum (∘ⱽ-distr-+ⱽ z x y) ⟩
      sum (z ∘ⱽ x +ⱽ z ∘ⱽ y)
      ≡⟨ sumProperties.sum-distr-+ⱽ (z ∘ⱽ x) (z ∘ⱽ y) ⟩
      sum (z ∘ⱽ x) + sum (z ∘ⱽ y)
      ≡⟨⟩
      ⟨ z , x ⟩ + ⟨ z , y ⟩
      ≡⟨ cong (_+ ⟨ z , y ⟩) (⟨⟩-comm z x) ⟩
      ⟨ x , z ⟩ + ⟨ z , y ⟩
      ≡⟨ cong (⟨ x , z ⟩ +_ ) (⟨⟩-comm z y) ⟩
      ⟨ x , z ⟩ + ⟨ y , z ⟩
      ∎

    ⟨x,y+z⟩≡⟨x,y⟩+⟨x,z⟩ : (x y z : Vec A n)
                        → ⟨ x , y +ⱽ z ⟩ ≡ (⟨ x , y ⟩) + (⟨ x , z ⟩)
    ⟨x,y+z⟩≡⟨x,y⟩+⟨x,z⟩ x y z = begin
      ⟨ x , y +ⱽ z ⟩
      ≡⟨ ⟨⟩-comm x (y +ⱽ z) ⟩
      ⟨ y +ⱽ z , x ⟩
      ≡⟨ ⟨x+y,z⟩≡⟨x,z⟩+⟨y,z⟩ y z x ⟩
      ⟨ y , x ⟩ + ⟨ z , x ⟩
      ≡⟨ cong (_+ ⟨ z , x ⟩) (⟨⟩-comm y x) ⟩
      ⟨ x , y ⟩ + ⟨ z , x ⟩
      ≡⟨ cong (⟨ x , y ⟩ +_ ) (⟨⟩-comm z x) ⟩
      ⟨ x , y ⟩ + ⟨ x , z ⟩
      ∎

open ⟨⟩-Properties public
