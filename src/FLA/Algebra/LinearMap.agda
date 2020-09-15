{-# OPTIONS --without-K --safe #-}

-- We do not parameterize this module since we do not have access to _+_ or _*_
-- for the fields that we want (real numbers)
open import Level using (Level)

open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open ≡-Reasoning

open import Data.Nat using (ℕ; suc; zero) renaming (_+_ to _+ᴺ_)
open import Data.Nat.Properties
open import Data.Vec using (Vec; foldr; zipWith; map; _++_; []; _∷_; take; drop)
open import Data.Vec.Properties

open import Function using (id)

open import FLA.Algebra.Structures
open import FLA.Algebra.Properties.Field
open import FLA.Algebra.LinearAlgebra
open import FLA.Algebra.LinearAlgebra.Properties
open import FLA.Data.VectorList using (split)
open import FLA.Data.Vec.Properties

module FLA.Algebra.LinearMap where

private
  variable
    ℓ : Level
    A : Set ℓ
    m n p q : ℕ

-- A linear map from one vector field to another
record _⊸_ {ℓ : Level} {A : Set ℓ} ⦃ F : Field A ⦄ (m n : ℕ) : Set ℓ where
  field
    f : (Vec A m → Vec A n)

    -- Additivity
    f[u+v]≡f[u]+f[v] : (u v : Vec A m) → f (u +ⱽ v) ≡ f u +ⱽ f v

    -- Homogeneity
    f[c*v]≡c*f[v] : (c : A) → (v : Vec A m) → f (c *ᶜ v) ≡ c *ᶜ (f v)

infixr 1 _⊸_

-- A convenient syntax if a particular set needs to be specified.
_—_⊸_ : {ℓ : Level} (m : ℕ) (A : Set ℓ) (n : ℕ) ⦃ F : Field A ⦄ → Set ℓ
m — A ⊸ n  = _⊸_ {A = A} m n
infixr 1 _—_⊸_

module _ ⦃ F : Field A ⦄ where
  open Field F
  open _⊸_

  _·ˡᵐ_ : m ⊸ n → Vec A m → Vec A n
  _·ˡᵐ_ LM = f LM

  _+ˡᵐ_ : m ⊸ n → m ⊸ n → m ⊸ n
  g +ˡᵐ h = record
    { f = λ v → g ·ˡᵐ v +ⱽ h ·ˡᵐ v
    ; f[u+v]≡f[u]+f[v] = f[u+v]≡f[u]+f[v]' g h
    ; f[c*v]≡c*f[v] = f[c*v]≡c*f[v]' g h
    }
    where
      f[u+v]≡f[u]+f[v]' : (g h : m ⊸ n) → (u v : Vec A m)
                        → g ·ˡᵐ (u +ⱽ v) +ⱽ h ·ˡᵐ (u +ⱽ v) ≡
                           g ·ˡᵐ u +ⱽ h ·ˡᵐ u +ⱽ (g ·ˡᵐ v +ⱽ h ·ˡᵐ v)
      f[u+v]≡f[u]+f[v]' g h u v rewrite
          f[u+v]≡f[u]+f[v] g u v
        | f[u+v]≡f[u]+f[v] h u v
        | (+ⱽ-assoc (g ·ˡᵐ u) (g ·ˡᵐ v) (h ·ˡᵐ u +ⱽ h ·ˡᵐ v))
        | sym (+ⱽ-assoc (g ·ˡᵐ v) (h ·ˡᵐ u) (h ·ˡᵐ v))
        | +ⱽ-comm (g ·ˡᵐ v) (h ·ˡᵐ u)
        | (+ⱽ-assoc (h ·ˡᵐ u) (g ·ˡᵐ v) (h ·ˡᵐ v))
        | sym (+ⱽ-assoc (g ·ˡᵐ u) (h ·ˡᵐ u) (g ·ˡᵐ v +ⱽ h ·ˡᵐ v))
        = refl
  
      f[c*v]≡c*f[v]' : (g h : m ⊸ n) → (c : A) (v : Vec A m)
                     → g ·ˡᵐ (c *ᶜ v) +ⱽ h ·ˡᵐ (c *ᶜ v) ≡
                        c *ᶜ (g ·ˡᵐ v +ⱽ h ·ˡᵐ v)
      f[c*v]≡c*f[v]' g h c v rewrite
          f[c*v]≡c*f[v] g c v
        | f[c*v]≡c*f[v] h c v
        | sym (*ᶜ-distr-+ⱽ c (g ·ˡᵐ v) (h ·ˡᵐ v))
        = refl

  _*ˡᵐ_ : n ⊸ p → m ⊸ n → m ⊸ p
  g *ˡᵐ h = record
    { f = λ v → g ·ˡᵐ (h ·ˡᵐ v)
    ; f[u+v]≡f[u]+f[v] = f[u+v]≡f[u]+f[v]' g h
    ; f[c*v]≡c*f[v] = f[c*v]≡c*f[v]' g h
    }
    where
      f[u+v]≡f[u]+f[v]' : (g : n ⊸ p) (h : m ⊸ n)
                        → (u v : Vec A m)
                        → g ·ˡᵐ (h ·ˡᵐ (u +ⱽ v)) ≡
                           g ·ˡᵐ (h ·ˡᵐ u) +ⱽ g ·ˡᵐ (h ·ˡᵐ v)
      f[u+v]≡f[u]+f[v]' g h u v rewrite
          f[u+v]≡f[u]+f[v] h u v
        | f[u+v]≡f[u]+f[v] g (f h u) (f h v)
        = refl
  
      f[c*v]≡c*f[v]' : (g : n ⊸ p) (h : m ⊸ n)
                     → (c : A) (v : Vec A m)
                     → g ·ˡᵐ (h ·ˡᵐ (c *ᶜ v)) ≡ c *ᶜ g ·ˡᵐ (h ·ˡᵐ v)
      f[c*v]≡c*f[v]' g h c v rewrite
          f[c*v]≡c*f[v] h c v
        | f[c*v]≡c*f[v] g c (h ·ˡᵐ v)
        = refl

  -- vertical stack forward operator
  _—ˡᵐ_ : p ⊸ m → p ⊸ n → p ⊸ (m +ᴺ n)
  T —ˡᵐ B =
    record
      { f = λ v →  T ·ˡᵐ v ++ B ·ˡᵐ v
      ; f[u+v]≡f[u]+f[v] = f[u+v]≡f[u]+f[v]' T B
      ; f[c*v]≡c*f[v] = f[c*v]≡c*f[v]' T B
      }
    where
      f[u+v]≡f[u]+f[v]' : (T : p ⊸ m) (B : p ⊸ n)
                        → (u v : Vec A p)
                        → T ·ˡᵐ (u +ⱽ v) ++ B ·ˡᵐ (u +ⱽ v) ≡
                          (T ·ˡᵐ u ++ B ·ˡᵐ u) +ⱽ (T ·ˡᵐ v ++ B ·ˡᵐ v)
      f[u+v]≡f[u]+f[v]' T B u v rewrite
          f[u+v]≡f[u]+f[v] T u v
        | f[u+v]≡f[u]+f[v] B u v
        | +ⱽ-flip-++ (T ·ˡᵐ u) (T ·ˡᵐ v) (B ·ˡᵐ u) (B ·ˡᵐ v)
        = refl

      f[c*v]≡c*f[v]' : (T : p ⊸ m) (B : p ⊸ n)
                     → (c : A) → (v : Vec A p)
                     → T ·ˡᵐ (c *ᶜ v) ++ B ·ˡᵐ (c *ᶜ v) ≡
                        c *ᶜ (T ·ˡᵐ v ++ B ·ˡᵐ v)
      f[c*v]≡c*f[v]' T B c v rewrite
          f[c*v]≡c*f[v] T c v
        | f[c*v]≡c*f[v] B c v
        | *ᶜ-distr-++ c (T ·ˡᵐ v) (B ·ˡᵐ v)
        = refl

  -- horizontal stack forward operator
  _|ˡᵐ_ : m ⊸ p → n ⊸ p → (m +ᴺ n) ⊸ p
  _|ˡᵐ_ {m} {n} {p} T B =
    record
      { f = λ v → T ·ˡᵐ (take m v) +ⱽ B ·ˡᵐ (drop m v)
      ; f[u+v]≡f[u]+f[v] = f[u+v]≡f[u]+f[v]' T B
      ; f[c*v]≡c*f[v] = f[c*v]≡c*f[v]' T B
      }
      where
        f[u+v]≡f[u]+f[v]' : {m n p : ℕ}
                          → (T : m ⊸ p) (B : n ⊸ p)
                          → (u v : Vec A (m +ᴺ n))
                          → T ·ˡᵐ take m (u +ⱽ v) +ⱽ B ·ˡᵐ drop m (u +ⱽ v) ≡
                             T ·ˡᵐ take m u +ⱽ B ·ˡᵐ drop m u +ⱽ
                             (T ·ˡᵐ take m v +ⱽ B ·ˡᵐ drop m v)
        f[u+v]≡f[u]+f[v]' {m} T B u v = begin
            T ·ˡᵐ (take m (u +ⱽ v)) +ⱽ B ·ˡᵐ (drop m (u +ⱽ v))
          ≡⟨ cong₂ (λ x y → T ·ˡᵐ x +ⱽ B ·ˡᵐ y)
                   (take-distr-zipWith _+_ u v) (drop-distr-zipWith _+_ u v)⟩
            T ·ˡᵐ (take m u +ⱽ take m v) +ⱽ B ·ˡᵐ (drop m u +ⱽ drop m v)
          ≡⟨ cong₂ _+ⱽ_ (f[u+v]≡f[u]+f[v] T (take m u) (take m v))
                        (f[u+v]≡f[u]+f[v] B (drop m u) (drop m v)) ⟩
            T ·ˡᵐ take m u +ⱽ T ·ˡᵐ take m v +ⱽ
            (B ·ˡᵐ drop m u +ⱽ B ·ˡᵐ drop m v)
          ≡⟨ sym (+ⱽ-assoc (T ·ˡᵐ take m u +ⱽ T ·ˡᵐ take m v)
                           (B ·ˡᵐ drop m u) (B ·ˡᵐ drop m v)) ⟩
            T ·ˡᵐ take m u +ⱽ T ·ˡᵐ take m v +ⱽ B ·ˡᵐ drop m u +ⱽ
            B ·ˡᵐ drop m v
          ≡⟨ cong (_+ⱽ B ·ˡᵐ drop m v) (+ⱽ-assoc (T ·ˡᵐ take m u)
                                                 (T ·ˡᵐ take m v)
                                                 (B ·ˡᵐ drop m u)) ⟩
            T ·ˡᵐ take m u +ⱽ (T ·ˡᵐ take m v +ⱽ B ·ˡᵐ drop m u) +ⱽ
            B ·ˡᵐ drop m v
          ≡⟨ cong (λ x → (T ·ˡᵐ take m u +ⱽ x) +ⱽ B ·ˡᵐ drop m v)
                  (+ⱽ-comm (T ·ˡᵐ take m v) (B ·ˡᵐ drop m u)) ⟩
            (T ·ˡᵐ take m u +ⱽ ((B ·ˡᵐ drop m u +ⱽ T ·ˡᵐ take m v))) +ⱽ
            B ·ˡᵐ drop m v
          ≡⟨ cong (_+ⱽ B ·ˡᵐ drop m v) (sym (+ⱽ-assoc (T ·ˡᵐ take m u)
                                                      (B ·ˡᵐ drop m u)
                                                      (T ·ˡᵐ take m v))) ⟩
            (T ·ˡᵐ take m u +ⱽ B ·ˡᵐ drop m u +ⱽ T ·ˡᵐ take m v) +ⱽ
            B ·ˡᵐ drop m v
          ≡⟨ +ⱽ-assoc (T ·ˡᵐ take m u +ⱽ B ·ˡᵐ drop m u)
                      (T ·ˡᵐ take m v) (B ·ˡᵐ drop m v) ⟩
            T ·ˡᵐ take m u +ⱽ B ·ˡᵐ drop m u +ⱽ
            (T ·ˡᵐ take m v +ⱽ B ·ˡᵐ drop m v)
          ∎

        f[c*v]≡c*f[v]' : {m n p : ℕ}
                       → (T : m ⊸ p) → (B : n ⊸ p)
                       → (c : A) (v : Vec A (m +ᴺ n))
                       → T ·ˡᵐ take m (c *ᶜ v) +ⱽ B ·ˡᵐ drop m (c *ᶜ v) ≡
                          c *ᶜ (T ·ˡᵐ take m v +ⱽ B ·ˡᵐ drop m v)
        f[c*v]≡c*f[v]' {m} T B c v = begin
            T ·ˡᵐ take m (c *ᶜ v) +ⱽ B ·ˡᵐ drop m (c *ᶜ v)
          ≡⟨ cong₂ (λ x y → T ·ˡᵐ x +ⱽ B ·ˡᵐ y) (take-distr-map (c *_) m v)
                                                 (drop-distr-map (c *_) m v) ⟩
            T ·ˡᵐ (c *ᶜ take m v) +ⱽ B ·ˡᵐ (c *ᶜ drop m v)
          ≡⟨ cong₂ _+ⱽ_ (f[c*v]≡c*f[v] T c (take m v))
                        (f[c*v]≡c*f[v] B c (drop m v)) ⟩
            c *ᶜ (T ·ˡᵐ take m v) +ⱽ c *ᶜ (B ·ˡᵐ drop m v)
          ≡⟨ sym (*ᶜ-distr-+ⱽ c (T ·ˡᵐ take m v) (B ·ˡᵐ drop m v)) ⟩
            c *ᶜ (T ·ˡᵐ take m v +ⱽ B ·ˡᵐ drop m v)
          ∎

  -- block diagonal forward and adjoint operator
  _/ˡᵐ_ : m ⊸ n → p ⊸ q → (m +ᴺ p) ⊸ (n +ᴺ q)
  _/ˡᵐ_ {m} {n} {p} {q} T B =
    record
      { f = λ v → T ·ˡᵐ (take m v) ++ B ·ˡᵐ (drop m v)
      ; f[u+v]≡f[u]+f[v] = f[u+v]≡f[u]+f[v]' T B
      ; f[c*v]≡c*f[v] = f[c*v]≡c*f[v]' T B
      }
      where
        f[u+v]≡f[u]+f[v]' : {m n p q : ℕ}
                          → (T : m ⊸ n) (B : p ⊸ q)
                          → (u v : Vec A (m +ᴺ p))
                          → T ·ˡᵐ (take m (u +ⱽ v)) ++ B ·ˡᵐ (drop m (u +ⱽ v)) ≡
                             (T ·ˡᵐ (take m u) ++ B ·ˡᵐ (drop m u)) +ⱽ
                             (T ·ˡᵐ (take m v) ++ B ·ˡᵐ (drop m v))
        f[u+v]≡f[u]+f[v]' {m} T B u v =
          begin
              T ·ˡᵐ take m (u +ⱽ v) ++ B ·ˡᵐ drop m (u +ⱽ v)
            ≡⟨ cong₂ (λ x y → T ·ˡᵐ x ++ B ·ˡᵐ y)
                     (take-distr-zipWith _+_ u v) (drop-distr-zipWith _+_ u v)⟩
              T ·ˡᵐ (take m u +ⱽ take m v) ++ B ·ˡᵐ (drop m u +ⱽ drop m v)
            ≡⟨ cong₂ _++_ (f[u+v]≡f[u]+f[v] T (take m u) (take m v))
                          (f[u+v]≡f[u]+f[v] B (drop m u) (drop m v)) ⟩
              (T ·ˡᵐ take m u +ⱽ T ·ˡᵐ take m v) ++
              (B ·ˡᵐ drop m u +ⱽ B ·ˡᵐ drop m v)
            ≡⟨ sym (+ⱽ-flip-++ (T ·ˡᵐ take m u) (T ·ˡᵐ take m v)
                               (B ·ˡᵐ drop m u) (B ·ˡᵐ drop m v)) ⟩
              (T ·ˡᵐ take m u ++ B ·ˡᵐ drop m u) +ⱽ
              (T ·ˡᵐ take m v ++ B ·ˡᵐ drop m v)
          ∎

        f[c*v]≡c*f[v]' : {m n p q : ℕ}
                       → (T : m ⊸ n) (B : p ⊸ q)
                       → (c : A) (v : Vec A (m +ᴺ p))
                       → T ·ˡᵐ (take m (c *ᶜ v)) ++ B ·ˡᵐ (drop m (c *ᶜ v)) ≡
                          c *ᶜ (T ·ˡᵐ (take m v) ++ B ·ˡᵐ (drop m v))
        f[c*v]≡c*f[v]' {m} T B c v =
          begin
              T ·ˡᵐ take m (c *ᶜ v) ++ B ·ˡᵐ drop m (c *ᶜ v)
            ≡⟨ cong₂ (λ x y → T ·ˡᵐ x ++ B ·ˡᵐ y) (take-distr-map (c *_) m v)
                                                   (drop-distr-map (c *_) m v) ⟩
              T ·ˡᵐ (c *ᶜ take m v) ++ B ·ˡᵐ (c *ᶜ (drop m v))
            ≡⟨ cong₂ _++_ (f[c*v]≡c*f[v] T c (take m v))
                          (f[c*v]≡c*f[v] B c (drop m v)) ⟩
              c *ᶜ (T ·ˡᵐ take m v) ++ c *ᶜ (B ·ˡᵐ drop m v)
            ≡⟨ sym (*ᶜ-distr-++ c (T ·ˡᵐ take m v) (B ·ˡᵐ drop m v)) ⟩
              c *ᶜ (T ·ˡᵐ take m v ++ B ·ˡᵐ drop m v)
          ∎

  _∘ˡᵐ_ : A → n ⊸ m → n ⊸ m
  c ∘ˡᵐ m =
    record
      { f = λ v → c *ᶜ m ·ˡᵐ v
      ; f[u+v]≡f[u]+f[v] = λ u v → trans (cong (c *ᶜ_) (f[u+v]≡f[u]+f[v] m u v))
                                          (*ᶜ-distr-+ⱽ c (m ·ˡᵐ u) (m ·ˡᵐ v))
      ; f[c*v]≡c*f[v] = λ c₁ v → trans (cong (c *ᶜ_) (f[c*v]≡c*f[v] m c₁ v))
                                        (*ᶜ-comm c c₁ (f m v))
      }

  -- Choose 20 since function application is assumed higher than almost anything
  infixr 20 _·ˡᵐ_

  infixl 2 _—ˡᵐ_
  infixl 3 _|ˡᵐ_
  infixl 4 _/ˡᵐ_
  infixl 6 _+ˡᵐ_
  infixl 7 _*ˡᵐ_
  infixl 10 _∘ˡᵐ_


-- Example LinearMap values ---------------------------------------------------

module _ ⦃ F : Field A ⦄ where
  idₗₘ : n ⊸ n
  idₗₘ = record
    { f = id
    ; f[u+v]≡f[u]+f[v] = λ u v → refl
    ; f[c*v]≡c*f[v] = λ c v → refl
    }

  diagₗₘ : Vec A n → n ⊸ n
  diagₗₘ d = record
    { f = d ∘ⱽ_
    ; f[u+v]≡f[u]+f[v] = ∘ⱽ-distr-+ⱽ d
    ; f[c*v]≡c*f[v] = λ c v → ∘ⱽ*ᶜ≡*ᶜ∘ⱽ c d v
    }
