{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

open import Relation.Binary.PropositionalEquality hiding (∀-extensionality)
open ≡-Reasoning

open import Data.Nat using (ℕ; suc; zero)
open import Data.Vec using (Vec; foldr; zipWith; map; []; _∷_; _++_)

open import FLA.Algebra.Structures
open import FLA.Algebra.Properties.Field
open import FLA.Algebra.LinearAlgebra
open import FLA.Data.Vec.Properties

module FLA.Algebra.LinearAlgebra.Properties where

private
  variable
    ℓ : Level
    A : Set ℓ
    m n p q : ℕ

module _ ⦃ F : Field A ⦄ where
  open Field F

  +ⱽ-assoc : (v₁ v₂ v₃ : Vec A n)
           → v₁ +ⱽ v₂ +ⱽ v₃ ≡ v₁ +ⱽ (v₂ +ⱽ v₃)
  +ⱽ-assoc [] [] [] = refl
  +ⱽ-assoc (v₁ ∷ vs₁) (v₂ ∷ vs₂) (v₃ ∷ vs₃) rewrite
      +ⱽ-assoc vs₁ vs₂ vs₃
    | +-assoc v₁ v₂ v₃
      = refl

  +ⱽ-comm : (v₁ v₂ : Vec A n) → v₁ +ⱽ v₂ ≡ v₂ +ⱽ v₁
  +ⱽ-comm [] [] = refl
  +ⱽ-comm (x₁ ∷ vs₁) (x₂ ∷ vs₂) = begin
    x₁ + x₂ ∷ vs₁ +ⱽ vs₂
    ≡⟨ cong ((x₁ + x₂) ∷_) (+ⱽ-comm vs₁ vs₂) ⟩
    x₁ + x₂ ∷ vs₂ +ⱽ vs₁
    ≡⟨ cong (_∷ vs₂ +ⱽ vs₁) (+-comm x₁ x₂) ⟩
    x₂ + x₁ ∷ vs₂ +ⱽ vs₁
    ∎

  ∘ⱽ-assoc : (v₁ v₂ v₃ : Vec A n)
           → v₁ ∘ⱽ v₂ ∘ⱽ v₃ ≡ v₁ ∘ⱽ (v₂ ∘ⱽ v₃)
  ∘ⱽ-assoc [] [] [] = refl
  ∘ⱽ-assoc (v₁ ∷ vs₁) (v₂ ∷ vs₂) (v₃ ∷ vs₃) rewrite
      ∘ⱽ-assoc vs₁ vs₂ vs₃
    | *-assoc v₁ v₂ v₃
    = refl

  ∘ⱽ-comm : (v₁ v₂ : Vec A n) → v₁ ∘ⱽ v₂ ≡ v₂ ∘ⱽ v₁
  ∘ⱽ-comm [] [] = refl
  ∘ⱽ-comm (v₁ ∷ vs₁) (v₂ ∷ vs₂) rewrite
      ∘ⱽ-comm vs₁ vs₂
    | *-comm v₁ v₂
    = refl

  ∘ⱽ-distr-+ⱽ : (a u v : Vec A n)
              → a ∘ⱽ (u +ⱽ v) ≡ a ∘ⱽ u +ⱽ a ∘ⱽ v
  ∘ⱽ-distr-+ⱽ [] [] [] = refl
  ∘ⱽ-distr-+ⱽ (a ∷ as) (u ∷ us) (v ∷ vs) rewrite
      ∘ⱽ-distr-+ⱽ as us vs
    | *-distr-+ a u v
    = refl

  -- Homogeneity of degree 1 for linear maps
  ∘ⱽ*ᶜ≡*ᶜ∘ⱽ : (c : A) (u v : Vec A n)
            → u ∘ⱽ c *ᶜ v ≡ c *ᶜ (u ∘ⱽ v)
  ∘ⱽ*ᶜ≡*ᶜ∘ⱽ c [] [] = refl
  ∘ⱽ*ᶜ≡*ᶜ∘ⱽ c (u ∷ us) (v ∷ vs) rewrite
      ∘ⱽ*ᶜ≡*ᶜ∘ⱽ c us vs
    | *-assoc u c v
    | *-comm u c
    | sym (*-assoc c u v)
    = refl

  *ᶜ-distr-+ⱽ : (c : A) (u v : Vec A n)
              → c *ᶜ (u +ⱽ v) ≡ c *ᶜ u +ⱽ c *ᶜ v
  *ᶜ-distr-+ⱽ c [] [] = refl
  *ᶜ-distr-+ⱽ c (u ∷ us) (v ∷ vs) rewrite
      *ᶜ-distr-+ⱽ c us vs
    | *-distr-+ c u v
    = refl

  *ᶜ-comm : (a b : A) (v : Vec A n) → a *ᶜ (b *ᶜ v) ≡ b *ᶜ (a *ᶜ v)
  *ᶜ-comm a b [] = refl
  *ᶜ-comm a b (v ∷ vs) =
    begin
        a *ᶜ (b *ᶜ (v ∷ vs))
      ≡⟨⟩
        (a * (b * v)) ∷ a *ᶜ (b *ᶜ vs)
      ≡⟨ cong (_∷ a *ᶜ (b *ᶜ vs)) (trans (trans (*-assoc a b v)
                                         (cong (_* v) (*-comm a b)))
                                         (sym (*-assoc b a v))) ⟩
        (b * (a * v)) ∷ a *ᶜ (b *ᶜ vs)
      ≡⟨ cong ((b * (a * v)) ∷_) (*ᶜ-comm a b vs) ⟩
        b *ᶜ (a *ᶜ (v ∷ vs))
      ∎
 

  +ⱽ-flip-++ : (a b : Vec A n) → (c d : Vec A m)
             → (a ++ c) +ⱽ (b ++ d) ≡ a +ⱽ b ++ c +ⱽ d
  +ⱽ-flip-++ [] [] c d = refl
  +ⱽ-flip-++ (a ∷ as) (b ∷ bs) c d rewrite +ⱽ-flip-++ as bs c d = refl

  *ᶜ-distr-++ : (c : A) (a : Vec A n) (b : Vec A m)
              → c *ᶜ (a ++ b) ≡ (c *ᶜ a) ++ (c *ᶜ b)
  *ᶜ-distr-++ c [] b = refl
  *ᶜ-distr-++ c (a ∷ as) b rewrite *ᶜ-distr-++ c as b = refl

  ⟨⟩-comm : (v₁ v₂ : Vec A n)
          → ⟨ v₁ , v₂ ⟩ ≡ ⟨ v₂ , v₁ ⟩
  ⟨⟩-comm [] [] = refl
  ⟨⟩-comm (x₁ ∷ v₁) (x₂ ∷ v₂) rewrite
      ⟨⟩-comm v₁ v₂
    | *-comm x₁ x₂
    = refl

  sum-distr-+ⱽ : (v₁ v₂ : Vec A n) → sum (v₁ +ⱽ v₂) ≡ sum v₁ + sum v₂
  sum-distr-+ⱽ [] [] = sym (0ᶠ+0ᶠ≡0ᶠ)
  sum-distr-+ⱽ (v₁ ∷ vs₁) (v₂ ∷ vs₂) rewrite
      sum-distr-+ⱽ vs₁ vs₂
    | +-assoc (v₁ + v₂) (foldr (λ v → A) _+_ 0ᶠ vs₁) (foldr (λ v → A) _+_ 0ᶠ vs₂)
    | sym (+-assoc v₁ v₂ (foldr (λ v → A) _+_ 0ᶠ vs₁))
    | +-comm v₂ (foldr (λ v → A) _+_ 0ᶠ vs₁)
    | +-assoc v₁ (foldr (λ v → A) _+_ 0ᶠ vs₁) v₂
    | sym (+-assoc (v₁ + (foldr (λ v → A) _+_ 0ᶠ vs₁)) v₂ (foldr (λ v → A) _+_ 0ᶠ vs₂))
    = refl

  -- Should we show bilinearity?
  --   ∀ λ ∈ F, B(λv, w) ≡ B(v, λw) ≡ λB(v, w)
  --   B(v₁ + v₂, w) ≡ B(v₁, w) + B(v₂, w) ∧ B(v, w₁ + w₂) ≡ B(v, w₁) + B(v, w₂)
  -- Additivity in both arguments
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
    ≡⟨ sum-distr-+ⱽ (z ∘ⱽ x) (z ∘ⱽ y) ⟩
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
  ⟨x,y+z⟩≡⟨x,y⟩+⟨x,z⟩ x y z =
    begin
      ⟨ x , y +ⱽ z ⟩        ≡⟨ ⟨⟩-comm x (y +ⱽ z) ⟩
      ⟨ y +ⱽ z , x ⟩        ≡⟨ ⟨x+y,z⟩≡⟨x,z⟩+⟨y,z⟩ y z x ⟩
      ⟨ y , x ⟩ + ⟨ z , x ⟩ ≡⟨ cong (_+ ⟨ z , x ⟩) (⟨⟩-comm y x) ⟩
      ⟨ x , y ⟩ + ⟨ z , x ⟩ ≡⟨ cong (⟨ x , y ⟩ +_ ) (⟨⟩-comm z x) ⟩
      ⟨ x , y ⟩ + ⟨ x , z ⟩ ∎

  ⟨a++b,c++d⟩≡⟨a,c⟩+⟨b,d⟩ : (a : Vec A m) → (b : Vec A n) → (c : Vec A m) → (d : Vec A n)
                          → ⟨ a ++ b , c ++ d ⟩ ≡ ⟨ a , c ⟩ + ⟨ b ,  d ⟩
  ⟨a++b,c++d⟩≡⟨a,c⟩+⟨b,d⟩ [] b [] d rewrite 0-+ (⟨ b , d ⟩) = refl
  ⟨a++b,c++d⟩≡⟨a,c⟩+⟨b,d⟩ (a ∷ as) b (c ∷ cs) d =
    begin
        ⟨ a ∷ as ++ b , c ∷ cs ++ d ⟩
      ≡⟨⟩
        (a * c) + ⟨ as ++ b , cs ++ d ⟩
      ≡⟨ cong ((a * c) +_) (⟨a++b,c++d⟩≡⟨a,c⟩+⟨b,d⟩ as b cs d) ⟩
        (a * c) + (⟨ as , cs ⟩ + ⟨ b , d ⟩)
      ≡⟨ +-assoc (a * c) ⟨ as , cs ⟩ ⟨ b , d ⟩ ⟩
        ((a * c) + ⟨ as , cs ⟩) + ⟨ b , d ⟩
      ≡⟨⟩
        ⟨ a ∷ as , c ∷ cs ⟩ + ⟨ b , d ⟩
    ∎

  ⟨a,b⟩+⟨c,d⟩≡⟨a++c,b++d⟩ : (a b : Vec A m) → (c d : Vec A n)
                          → ⟨ a , b ⟩ + ⟨ c ,  d ⟩ ≡ ⟨ a ++ c , b ++ d ⟩
  ⟨a,b⟩+⟨c,d⟩≡⟨a++c,b++d⟩ a b c d = sym (⟨a++b,c++d⟩≡⟨a,c⟩+⟨b,d⟩ a c b d)
