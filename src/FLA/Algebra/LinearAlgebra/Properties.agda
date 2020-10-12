{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; []; _∷_; _++_; foldr; map; replicate)

open import FLA.Algebra.Structures
open import FLA.Algebra.Properties.Field
open import FLA.Algebra.LinearAlgebra

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
  +ⱽ-comm (x₁ ∷ vs₁) (x₂ ∷ vs₂) =
    begin
      x₁ + x₂ ∷ vs₁ +ⱽ vs₂ ≡⟨ cong ((x₁ + x₂) ∷_) (+ⱽ-comm vs₁ vs₂) ⟩
      x₁ + x₂ ∷ vs₂ +ⱽ vs₁ ≡⟨ cong (_∷ vs₂ +ⱽ vs₁) (+-comm x₁ x₂) ⟩
      x₂ + x₁ ∷ vs₂ +ⱽ vs₁ ∎

  v+0ᶠⱽ≡v : (v : Vec A n) → v +ⱽ (replicate 0ᶠ) ≡ v
  v+0ᶠⱽ≡v [] = refl
  v+0ᶠⱽ≡v (v ∷ vs) = cong₂ _∷_ (+-0 v) (v+0ᶠⱽ≡v vs)

  0ᶠⱽ+v≡v : (v : Vec A n) → (replicate 0ᶠ) +ⱽ v ≡ v
  0ᶠⱽ+v≡v v = trans (+ⱽ-comm (replicate 0ᶠ) v) (v+0ᶠⱽ≡v v)

  -- This should work for any linear function (I think), instead of just -_,
  *ⱽ-map--ⱽ : (a v : Vec A n)
            → a *ⱽ (map -_ v) ≡ map -_ (a *ⱽ v)
  *ⱽ-map--ⱽ [] [] = refl
  *ⱽ-map--ⱽ (a ∷ as) (v ∷ vs) = begin
      (a ∷ as) *ⱽ map -_ (v ∷ vs)
    ≡⟨⟩
      (a * - v) ∷ (as *ⱽ map -_ vs)
    ≡⟨ cong ((a * - v) ∷_) (*ⱽ-map--ⱽ as vs) ⟩
      (a * - v) ∷ (map -_ (as *ⱽ vs))
    ≡⟨ cong (_∷ (map -_ (as *ⱽ vs))) (a*-b≡-[a*b] a v) ⟩
      (- (a * v)) ∷ (map -_ (as *ⱽ vs))
    ≡⟨⟩
      map -_ ((a ∷ as) *ⱽ (v ∷ vs))
    ∎

  -ⱽ≡-1ᶠ∘ⱽ : (v : Vec A n) → map -_ v ≡ (- 1ᶠ) ∘ⱽ v
  -ⱽ≡-1ᶠ∘ⱽ [] = refl
  -ⱽ≡-1ᶠ∘ⱽ (v ∷ vs) = begin
      map -_ (v ∷ vs)           ≡⟨⟩
      (- v) ∷ map -_ vs         ≡⟨ cong₂ (_∷_) (-a≡-1ᶠ*a v) (-ⱽ≡-1ᶠ∘ⱽ vs) ⟩
      (- 1ᶠ * v) ∷ (- 1ᶠ) ∘ⱽ vs ≡⟨⟩
      (- 1ᶠ) ∘ⱽ (v ∷ vs)        ∎

  *ⱽ-assoc : (v₁ v₂ v₃ : Vec A n)
           → v₁ *ⱽ v₂ *ⱽ v₃ ≡ v₁ *ⱽ (v₂ *ⱽ v₃)
  *ⱽ-assoc [] [] [] = refl
  *ⱽ-assoc (v₁ ∷ vs₁) (v₂ ∷ vs₂) (v₃ ∷ vs₃) rewrite
      *ⱽ-assoc vs₁ vs₂ vs₃
    | *-assoc v₁ v₂ v₃
    = refl

  *ⱽ-comm : (v₁ v₂ : Vec A n) → v₁ *ⱽ v₂ ≡ v₂ *ⱽ v₁
  *ⱽ-comm [] [] = refl
  *ⱽ-comm (v₁ ∷ vs₁) (v₂ ∷ vs₂) rewrite
      *ⱽ-comm vs₁ vs₂
    | *-comm v₁ v₂
    = refl

  *ⱽ-distr-+ⱽ : (a u v : Vec A n)
              → a *ⱽ (u +ⱽ v) ≡ a *ⱽ u +ⱽ a *ⱽ v
  *ⱽ-distr-+ⱽ [] [] [] = refl
  *ⱽ-distr-+ⱽ (a ∷ as) (u ∷ us) (v ∷ vs) rewrite
      *ⱽ-distr-+ⱽ as us vs
    | *-distr-+ a u v
    = refl

  *ⱽ-distr--ⱽ : (a u v : Vec A n)
              → a *ⱽ (u -ⱽ v) ≡ a *ⱽ u -ⱽ a *ⱽ v
  *ⱽ-distr--ⱽ a u v = begin
    a *ⱽ (u -ⱽ v)               ≡⟨⟩
    a *ⱽ (u +ⱽ (map (-_) v))    ≡⟨ *ⱽ-distr-+ⱽ a u (map -_ v) ⟩
    a *ⱽ u +ⱽ a *ⱽ (map -_ v)   ≡⟨ cong (a *ⱽ u +ⱽ_) (*ⱽ-map--ⱽ a v) ⟩
    a *ⱽ u +ⱽ (map -_ (a *ⱽ v)) ≡⟨⟩
    a *ⱽ u -ⱽ a *ⱽ v            ∎

  -- Homogeneity of degree 1 for linear maps
  *ⱽ∘ⱽ≡∘ⱽ*ⱽ : (c : A) (u v : Vec A n)
            → u *ⱽ c ∘ⱽ v ≡ c ∘ⱽ (u *ⱽ v)
  *ⱽ∘ⱽ≡∘ⱽ*ⱽ c [] [] = refl
  *ⱽ∘ⱽ≡∘ⱽ*ⱽ c (u ∷ us) (v ∷ vs) rewrite
      *ⱽ∘ⱽ≡∘ⱽ*ⱽ c us vs
    | *-assoc u c v
    | *-comm u c
    | sym (*-assoc c u v)
    = refl

  ∘ⱽ*ⱽ-assoc : (c : A) (u v : Vec A n)
             → c ∘ⱽ (u *ⱽ v) ≡ (c ∘ⱽ u) *ⱽ v
  ∘ⱽ*ⱽ-assoc c [] [] = refl
  ∘ⱽ*ⱽ-assoc c (u ∷ us) (v ∷ vs) = cong₂ (_∷_) (*-assoc c u v)
                                               (∘ⱽ*ⱽ-assoc c us vs)

  ∘ⱽ-distr-+ⱽ : (c : A) (u v : Vec A n)
              → c ∘ⱽ (u +ⱽ v) ≡ c ∘ⱽ u +ⱽ c ∘ⱽ v
  ∘ⱽ-distr-+ⱽ c [] [] = refl
  ∘ⱽ-distr-+ⱽ c (u ∷ us) (v ∷ vs) rewrite
      ∘ⱽ-distr-+ⱽ c us vs
    | *-distr-+ c u v
    = refl

  ∘ⱽ-comm : (a b : A) (v : Vec A n) → a ∘ⱽ (b ∘ⱽ v) ≡ b ∘ⱽ (a ∘ⱽ v)
  ∘ⱽ-comm a b [] = refl
  ∘ⱽ-comm a b (v ∷ vs) = cong₂ _∷_ (trans (trans (*-assoc a b v)
                                          (cong (_* v) (*-comm a b)))
                                          (sym (*-assoc b a v)))
                                   (∘ⱽ-comm a b vs)

  +ⱽ-flip-++ : (a b : Vec A n) → (c d : Vec A m)
             → (a ++ c) +ⱽ (b ++ d) ≡ a +ⱽ b ++ c +ⱽ d
  +ⱽ-flip-++ [] [] c d = refl
  +ⱽ-flip-++ (a ∷ as) (b ∷ bs) c d rewrite +ⱽ-flip-++ as bs c d = refl

  ∘ⱽ-distr-++ : (c : A) (a : Vec A n) (b : Vec A m)
              → c ∘ⱽ (a ++ b) ≡ (c ∘ⱽ a) ++ (c ∘ⱽ b)
  ∘ⱽ-distr-++ c [] b = refl
  ∘ⱽ-distr-++ c (a ∷ as) b rewrite ∘ⱽ-distr-++ c as b = refl

  ⟨⟩-comm : (v₁ v₂ : Vec A n)
          → ⟨ v₁ , v₂ ⟩ ≡ ⟨ v₂ , v₁ ⟩
  ⟨⟩-comm v₁ v₂ = cong sum (*ⱽ-comm v₁ v₂)

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
    sum ((x +ⱽ y) *ⱽ z )
    ≡⟨ cong sum (*ⱽ-comm (x +ⱽ y) z) ⟩
    sum (z *ⱽ (x +ⱽ y))
    ≡⟨ cong sum (*ⱽ-distr-+ⱽ z x y) ⟩
    sum (z *ⱽ x +ⱽ z *ⱽ y)
    ≡⟨ sum-distr-+ⱽ (z *ⱽ x) (z *ⱽ y) ⟩
    sum (z *ⱽ x) + sum (z *ⱽ y)
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
