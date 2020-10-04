{-# OPTIONS --without-K --safe #-}

open import Level using (Level)
open import Data.Nat using (ℕ) renaming (_+_ to _+ᴺ_)

open import Data.Vec using (Vec; _++_; take; drop)

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Function using (id)

open import FLA.Algebra.Structures
open import FLA.Algebra.Properties.Field
open import FLA.Algebra.LinearMap
open import FLA.Algebra.LinearAlgebra
open import FLA.Algebra.LinearAlgebra.Properties
open import FLA.Data.Vec.Properties

module FLA.Algebra.LinearAlgebra.Matrix where

private
  variable
    ℓ : Level
    A : Set ℓ
    m n p q : ℕ


-------------------------------------------------------------------------------
--                          M constructor and values                         --
-------------------------------------------------------------------------------

data Mat_×_ {A : Set ℓ} ⦃ F : Field A ⦄ (m n : ℕ) : Set ℓ where
  ⟦_,_,_⟧ : (M : n ⊸ m )
          → (Mᵀ : m ⊸ n )
          → (p : (x : Vec A m) → (y : Vec A n)
               → ⟨ x , M ·ˡᵐ y ⟩ ≡ ⟨ y , Mᵀ ·ˡᵐ x ⟩ )
          → Mat m × n

module _ ⦃ F : Field A ⦄ where

  _ᵀ : Mat m × n → Mat n × m
  ⟦ f , a , p ⟧ ᵀ = ⟦ a , f , (λ x y → sym (p y x)) ⟧

  _·ᴹₗ_ : Mat m × n → Vec A n → Vec A m
  ⟦ f , _ , _ ⟧ ·ᴹₗ x = f ·ˡᵐ x

  _·ᴹᵣ_ : Vec A m → Mat m × n → Vec A n
  x ·ᴹᵣ ⟦ _ , a , _ ⟧ = a ·ˡᵐ x

  infixr 20 _·ᴹᵣ_
  infixr 21 _·ᴹₗ_
  infixl 25 _ᵀ


module _ ⦃ F : Field A ⦄ where
  open Field F
  open _⊸_

  _+ᴹ_ : Mat m × n → Mat m × n → Mat m × n
  ⟦ M₁ , M₁ᵀ , p₁ ⟧ +ᴹ ⟦ M₂ , M₂ᵀ , p₂ ⟧ =
    ⟦ M₁ +ˡᵐ M₂
    , M₁ᵀ +ˡᵐ M₂ᵀ
    , ⟨⟩-proof M₁ M₂ M₁ᵀ M₂ᵀ p₁ p₂
    ⟧
    where
      ⟨⟩-proof : (M₁ M₂ : n ⊸ m) (M₁ᵀ M₂ᵀ : m ⊸ n)
               → (M₁-⟨⟩-proof : (x : Vec A m) (y : Vec A n)
                               → ⟨ x , M₁ ·ˡᵐ y ⟩ ≡ ⟨ y , M₁ᵀ ·ˡᵐ x ⟩ )
               → (M₂-⟨⟩-proof : (x : Vec A m) (y : Vec A n)
                               → ⟨ x , M₂ ·ˡᵐ y ⟩ ≡ ⟨ y , M₂ᵀ ·ˡᵐ x ⟩ )
               → (x : Vec A m) (y : Vec A n)
               → ⟨ x , (M₁ +ˡᵐ M₂) ·ˡᵐ y ⟩ ≡ ⟨ y , (M₁ᵀ +ˡᵐ M₂ᵀ) ·ˡᵐ x ⟩
      ⟨⟩-proof M₁ M₂ M₁ᵀ M₂ᵀ M₁-proof M₂-proof x y =
        begin
            ⟨ x , (M₁ +ˡᵐ M₂) ·ˡᵐ y ⟩
          ≡⟨⟩
            ⟨ x , M₁ ·ˡᵐ y +ⱽ M₂ ·ˡᵐ y ⟩
          ≡⟨ ⟨x,y+z⟩≡⟨x,y⟩+⟨x,z⟩ x (M₁ ·ˡᵐ y) (M₂ ·ˡᵐ y) ⟩
            ⟨ x , M₁ ·ˡᵐ y ⟩ + ⟨ x , M₂ ·ˡᵐ y ⟩
          ≡⟨ cong (_+ ⟨ x , M₂ ·ˡᵐ y ⟩) (M₁-proof x y) ⟩
            ⟨ y , M₁ᵀ ·ˡᵐ x ⟩ + ⟨ x , M₂ ·ˡᵐ y ⟩
          ≡⟨ cong (⟨ y , M₁ᵀ ·ˡᵐ x ⟩ +_) (M₂-proof x y) ⟩
            ⟨ y , M₁ᵀ ·ˡᵐ x ⟩ + ⟨ y , M₂ᵀ ·ˡᵐ x ⟩
          ≡⟨ sym (⟨x,y+z⟩≡⟨x,y⟩+⟨x,z⟩ y (M₁ᵀ ·ˡᵐ x) (M₂ᵀ ·ˡᵐ x)) ⟩
            ⟨ y , (M₁ᵀ +ˡᵐ M₂ᵀ) ·ˡᵐ x ⟩
        ∎

  _*ᴹ_ : Mat m × n → Mat n × p → Mat m × p
  ⟦ M₁ , M₁ᵀ , p₁ ⟧ *ᴹ ⟦ M₂ , M₂ᵀ , p₂ ⟧ =
    ⟦ M₁ *ˡᵐ M₂
    , M₂ᵀ *ˡᵐ M₁ᵀ
    , ⟨⟩-proof M₁ M₂ M₁ᵀ M₂ᵀ p₁ p₂
    ⟧
    where
      ⟨⟩-proof : (M₁ : n ⊸ m) (M₂ : p ⊸ n) (M₁ᵀ : m ⊸ n) (M₂ᵀ : n ⊸ p)
               → (M₁-⟨⟩-proof : (x : Vec A m) (y : Vec A n)
                               → ⟨ x , M₁ ·ˡᵐ y ⟩ ≡ ⟨ y , M₁ᵀ ·ˡᵐ x ⟩ )
               → (M₂-⟨⟩-proof : (x : Vec A n) (y : Vec A p)
                               → ⟨ x , M₂ ·ˡᵐ y ⟩ ≡ ⟨ y , M₂ᵀ ·ˡᵐ x ⟩ )
               → (x : Vec A m) (y : Vec A p)
               → ⟨ x , (M₁ *ˡᵐ M₂) ·ˡᵐ y ⟩ ≡ ⟨ y , (M₂ᵀ *ˡᵐ M₁ᵀ) ·ˡᵐ x ⟩
      ⟨⟩-proof M₁ M₂ M₁ᵀ M₂ᵀ M₁-proof M₂-proof x y =
        begin
          ⟨ x , (M₁ *ˡᵐ M₂) ·ˡᵐ y ⟩   ≡⟨⟩
          ⟨ x , M₁ ·ˡᵐ M₂ ·ˡᵐ y ⟩     ≡⟨ M₁-proof x (M₂ ·ˡᵐ y) ⟩
          ⟨ M₂ ·ˡᵐ y , M₁ᵀ ·ˡᵐ x ⟩    ≡⟨ ⟨⟩-comm (M₂ ·ˡᵐ y) (M₁ᵀ ·ˡᵐ x) ⟩
          ⟨ M₁ᵀ ·ˡᵐ x , M₂ ·ˡᵐ y ⟩    ≡⟨ M₂-proof (M₁ᵀ ·ˡᵐ x) y ⟩
          ⟨ y , (M₂ᵀ *ˡᵐ M₁ᵀ) ·ˡᵐ x ⟩ ∎

  _|ᴹ_ : Mat m × n → Mat m × p → Mat m × (n +ᴺ p)
  ⟦ M₁ , M₁ᵀ , p₁ ⟧ |ᴹ ⟦ M₂ , M₂ᵀ , p₂ ⟧ =
    ⟦ M₁ |ˡᵐ M₂
    , M₁ᵀ —ˡᵐ M₂ᵀ
    , ⟨⟩-proof M₁ M₂ M₁ᵀ M₂ᵀ p₁ p₂
    ⟧
    where
      ⟨⟩-proof : {m n p : ℕ}
               → (M₁ : n ⊸ m) (M₂ : p ⊸ m) (M₁ᵀ : m ⊸ n) (M₂ᵀ : m ⊸ p)
               → (M₁-⟨⟩-proof : (x : Vec A m) (y : Vec A n)
                               → ⟨ x , M₁ ·ˡᵐ y ⟩ ≡ ⟨ y , M₁ᵀ ·ˡᵐ x ⟩ )
               → (M₂-⟨⟩-proof : (x : Vec A m) (y : Vec A p)
                               → ⟨ x , M₂ ·ˡᵐ y ⟩ ≡ ⟨ y , M₂ᵀ ·ˡᵐ x ⟩ )
               → (x : Vec A m) (y : Vec A (n +ᴺ p)) →
                      ⟨ x , (M₁ |ˡᵐ M₂) ·ˡᵐ y ⟩ ≡ ⟨ y , (M₁ᵀ —ˡᵐ M₂ᵀ) ·ˡᵐ x ⟩
      ⟨⟩-proof {m} {n} {p} M₁ M₂ M₁ᵀ M₂ᵀ M₁-proof M₂-proof x y =
        begin
            ⟨ x , (M₁ |ˡᵐ M₂) ·ˡᵐ y ⟩
          ≡⟨⟩
            ⟨ x , M₁ ·ˡᵐ take n y +ⱽ M₂ ·ˡᵐ drop n y ⟩
          ≡⟨ ⟨x,y+z⟩≡⟨x,y⟩+⟨x,z⟩ x (M₁ ·ˡᵐ take n y) (M₂ ·ˡᵐ drop n y) ⟩
            ⟨ x , M₁ ·ˡᵐ take n y ⟩ + ⟨ x ,  M₂ ·ˡᵐ drop n y ⟩
          ≡⟨ cong₂ _+_ (M₁-proof x (take n y)) (M₂-proof x (drop n y)) ⟩
            ⟨ take n y , M₁ᵀ ·ˡᵐ x ⟩ + ⟨ drop n y ,  M₂ᵀ ·ˡᵐ x ⟩
          ≡⟨ ⟨a,b⟩+⟨c,d⟩≡⟨a++c,b++d⟩ (take n y) (M₁ᵀ ·ˡᵐ x)
                                     (drop n y) (M₂ᵀ ·ˡᵐ x) ⟩
            ⟨ take n y ++ drop n y , M₁ᵀ ·ˡᵐ x ++ M₂ᵀ ·ˡᵐ x ⟩
          ≡⟨ cong (λ a → ⟨ a , M₁ᵀ ·ˡᵐ x ++ M₂ᵀ ·ˡᵐ x ⟩) (take-drop-id n y) ⟩
            ⟨ y , M₁ᵀ ·ˡᵐ x ++ M₂ᵀ ·ˡᵐ x ⟩
          ≡⟨⟩
            ⟨ y , (M₁ᵀ —ˡᵐ M₂ᵀ) ·ˡᵐ x ⟩
        ∎

  _—ᴹ_ : Mat m × p → Mat n × p → Mat (m +ᴺ n) × p
  M —ᴹ N = (M ᵀ |ᴹ N ᵀ) ᵀ

  -- Block diagonal matrix
  _/ᴹ_ : Mat m × n → Mat p × q → Mat (m +ᴺ p) × (n +ᴺ q)
  ⟦ M₁ , M₁ᵀ , p₁ ⟧ /ᴹ ⟦ M₂ , M₂ᵀ , p₂ ⟧ =
    ⟦ M₁ /ˡᵐ M₂
    , M₁ᵀ /ˡᵐ M₂ᵀ
    , ⟨⟩-proof M₁ M₂ M₁ᵀ M₂ᵀ p₁ p₂
    ⟧
    where
      ⟨⟩-proof : {m n p q : ℕ}
               → (M₁ : n ⊸ m) (M₂ : q ⊸ p) (M₁ᵀ : m ⊸ n) (M₂ᵀ : p ⊸ q)
               → (M₁-⟨⟩-proof : (x : Vec A m) (y : Vec A n)
                               → ⟨ x , M₁ ·ˡᵐ y ⟩ ≡ ⟨ y , M₁ᵀ ·ˡᵐ x ⟩ )
               → (M₂-⟨⟩-proof : (x : Vec A p) (y : Vec A q)
                               → ⟨ x , M₂ ·ˡᵐ y ⟩ ≡ ⟨ y , M₂ᵀ ·ˡᵐ x ⟩ )
               → (x : Vec A (m +ᴺ p)) (y : Vec A (n +ᴺ q)) →
                        ⟨ x , (M₁ /ˡᵐ M₂) ·ˡᵐ y ⟩ ≡ ⟨ y , (M₁ᵀ /ˡᵐ M₂ᵀ) ·ˡᵐ x ⟩
      ⟨⟩-proof {m} {n} {p} M₁ M₂ M₁ᵀ M₂ᵀ M₁-proof M₂-proof x y =
        begin
            ⟨ x , (M₁ /ˡᵐ M₂) ·ˡᵐ y ⟩
          ≡⟨⟩
            ⟨ x , M₁ ·ˡᵐ take n y ++ M₂ ·ˡᵐ drop n y ⟩
          ≡⟨ cong (λ x → ⟨ x , M₁ ·ˡᵐ take n y ++ M₂ ·ˡᵐ drop n y ⟩)
                  (sym (take-drop-id m x)) ⟩
            ⟨ take m x ++ drop m x , M₁ ·ˡᵐ (take n y) ++ M₂ ·ˡᵐ drop n y ⟩
          ≡⟨ ⟨a++b,c++d⟩≡⟨a,c⟩+⟨b,d⟩ (take m x) (drop m x)
                                     (M₁ ·ˡᵐ (take n y)) (M₂ ·ˡᵐ drop n y) ⟩
            ⟨ take m x , M₁ ·ˡᵐ (take n y) ⟩ + ⟨ drop m x , M₂ ·ˡᵐ drop n y ⟩
          ≡⟨ cong₂ _+_ (M₁-proof (take m x) (take n y))
                       (M₂-proof (drop m x) (drop n y)) ⟩
            ⟨ take n y , M₁ᵀ ·ˡᵐ take m x  ⟩ + ⟨ drop n y , M₂ᵀ ·ˡᵐ  drop m x ⟩
          ≡⟨ ⟨a,b⟩+⟨c,d⟩≡⟨a++c,b++d⟩ (take n y) (M₁ᵀ ·ˡᵐ take m x)
                                     (drop n y) (M₂ᵀ ·ˡᵐ  drop m x) ⟩
            ⟨ take n y ++ drop n y , M₁ᵀ ·ˡᵐ take m x ++ M₂ᵀ ·ˡᵐ  drop m x ⟩
          ≡⟨ cong (λ y → ⟨ y , M₁ᵀ ·ˡᵐ take m x ++ M₂ᵀ ·ˡᵐ  drop m x ⟩)
                  (take-drop-id n y) ⟩
            ⟨ y , M₁ᵀ ·ˡᵐ (take m x) ++ M₂ᵀ ·ˡᵐ (drop m x) ⟩
          ≡⟨⟩
            ⟨ y , (M₁ᵀ /ˡᵐ M₂ᵀ) ·ˡᵐ x ⟩
        ∎

  -- Multiply by a constant
  _∘ᴹ_ : A → Mat m × n → Mat m × n
  c ∘ᴹ ⟦ M , Mᵀ , p ⟧ = ⟦ c ∘ˡᵐ M , c ∘ˡᵐ Mᵀ , ⟨⟩-proof M Mᵀ c p ⟧
    where
      ⟨⟩-proof : {m n : ℕ} (M : n ⊸ m) (Mᵀ : m ⊸ n) (c : A)
               → (M-⟨⟩-proof : (x : Vec A m) (y : Vec A n)
                               → ⟨ x , M ·ˡᵐ y ⟩ ≡ ⟨ y , Mᵀ ·ˡᵐ x ⟩ )
               → (x : Vec A m) (y : Vec A n)
               → ⟨ x , (c ∘ˡᵐ M) ·ˡᵐ y ⟩ ≡ ⟨ y , (c ∘ˡᵐ Mᵀ) ·ˡᵐ x ⟩
      ⟨⟩-proof {m} {n} M Mᵀ c M-⟨⟩-proof x y =
        begin
            ⟨ x , (c ∘ˡᵐ M) ·ˡᵐ y ⟩
          ≡⟨⟩
            ⟨ x , c ∘ⱽ (M ·ˡᵐ y) ⟩
          ≡⟨ cong (λ z → ⟨ x , z ⟩) (sym (f[c*v]≡c*f[v] M c y)) ⟩
            ⟨ x , M ·ˡᵐ (c ∘ⱽ y) ⟩
          ≡⟨ M-⟨⟩-proof x ((c ∘ⱽ y)) ⟩
            ⟨ c ∘ⱽ y , Mᵀ ·ˡᵐ x ⟩
          ≡⟨ ⟨⟩-comm (c ∘ⱽ y) (Mᵀ ·ˡᵐ x) ⟩
            ⟨ Mᵀ ·ˡᵐ x , c ∘ⱽ y ⟩
          ≡⟨ cong sum (trans (*ⱽ∘ⱽ≡∘ⱽ*ⱽ c (Mᵀ ·ˡᵐ x) y)
                             (∘ⱽ*ⱽ-assoc c (Mᵀ ·ˡᵐ x) y)) ⟩
            ⟨ (c ∘ˡᵐ Mᵀ) ·ˡᵐ x , y ⟩
          ≡⟨ ⟨⟩-comm ((c ∘ˡᵐ Mᵀ) ·ˡᵐ x) y ⟩
            ⟨ y , (c ∘ˡᵐ Mᵀ) ·ˡᵐ x ⟩
        ∎

  infixl 2 _—ᴹ_
  infixl 3 _|ᴹ_
  infixl 4 _/ᴹ_
  infixl 6 _+ᴹ_
  infixl 7 _*ᴹ_
  infixl 10 _∘ᴹ_


-- Matrix Free Operators ------------------------------------------------------

module _ ⦃ F : Field A ⦄ where
  open Field F

  I : Mat n × n
  I = ⟦ idₗₘ , idₗₘ , id-transpose  ⟧
    where
      id-transpose : (x y : Vec A n)
                   → ⟨ x , id y ⟩ ≡ ⟨ y , id x ⟩
      id-transpose x y rewrite
          zipWith-comm (_*_) (*-comm) x y
        = refl

  diag : Vec A n → Mat n × n
  diag d = ⟦ diagₗₘ d , diagₗₘ d , diag-transpose d ⟧
    where
      diag-transpose : (d : Vec A n) → (x y : Vec A n)
                     → ⟨ x , diagₗₘ d ·ˡᵐ y ⟩ ≡ ⟨ y , diagₗₘ d ·ˡᵐ x ⟩
      diag-transpose d x y =
        begin
          ⟨ x , diagₗₘ d ·ˡᵐ y ⟩ ≡⟨⟩
          sum (x *ⱽ (d *ⱽ y))    ≡⟨ cong (sum) (*ⱽ-comm x (d *ⱽ y)) ⟩
          sum ((d *ⱽ y) *ⱽ x)    ≡⟨ cong (λ dy → sum (dy *ⱽ x)) (*ⱽ-comm d y) ⟩
          sum ((y *ⱽ d) *ⱽ x)    ≡⟨ cong sum (*ⱽ-assoc y d x) ⟩
          sum (y *ⱽ (d *ⱽ x))    ≡⟨⟩
          ⟨ y , diagₗₘ d ·ˡᵐ x ⟩ ∎
