{-# OPTIONS --without-K --safe #-}

-- We do not parameterize this module since we do not have access to _+_ or _*_
-- for the fields that we want (real numbers)
open import Level using (Level)

open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open ≡-Reasoning

open import Data.Nat using (ℕ) renaming (_+_ to _+ᴺ_)
open import Data.Nat.Properties
open import Data.Vec using (Vec; []; _∷_; _++_; take; drop; map; replicate)

open import Function using (id)

open import FLA.Algebra.Structures
open import FLA.Algebra.Properties.Field
open import FLA.Algebra.LinearAlgebra
open import FLA.Algebra.LinearAlgebra.Properties
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
    f[c*v]≡c*f[v] : (c : A) → (v : Vec A m) → f (c ∘ⱽ v) ≡ c ∘ⱽ (f v)

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

  private
    +ˡᵐ-linearity : (g h : m ⊸ n) → (u v x y : Vec A m)
                  → g ·ˡᵐ (u +ⱽ v) +ⱽ h ·ˡᵐ (x +ⱽ y) ≡
                     g ·ˡᵐ u +ⱽ h ·ˡᵐ x +ⱽ (g ·ˡᵐ v +ⱽ h ·ˡᵐ y)
    +ˡᵐ-linearity g h u v x y rewrite
        f[u+v]≡f[u]+f[v] g u v
      | f[u+v]≡f[u]+f[v] h x y
      | (+ⱽ-assoc (g ·ˡᵐ u) (g ·ˡᵐ v) (h ·ˡᵐ x +ⱽ h ·ˡᵐ y))
      | sym (+ⱽ-assoc (g ·ˡᵐ v) (h ·ˡᵐ x) (h ·ˡᵐ y))
      | +ⱽ-comm (g ·ˡᵐ v) (h ·ˡᵐ x)
      | (+ⱽ-assoc (h ·ˡᵐ x) (g ·ˡᵐ v) (h ·ˡᵐ y))
      | sym (+ⱽ-assoc (g ·ˡᵐ u) (h ·ˡᵐ x) (g ·ˡᵐ v +ⱽ h ·ˡᵐ y))
      = refl

    +-homogeneity : (g h : m ⊸ n) → (c : A) (u v : Vec A m)
                  → g ·ˡᵐ (c ∘ⱽ u) +ⱽ h ·ˡᵐ (c ∘ⱽ v) ≡
                     c ∘ⱽ (g ·ˡᵐ u +ⱽ h ·ˡᵐ v)
    +-homogeneity g h c u v rewrite
          f[c*v]≡c*f[v] g c u
        | f[c*v]≡c*f[v] h c v
        | sym (∘ⱽ-distr-+ⱽ c (g ·ˡᵐ u) (h ·ˡᵐ v))
        = refl

  _+ˡᵐ_ : m ⊸ n → m ⊸ n → m ⊸ n
  g +ˡᵐ h = record
    { f = λ v → g ·ˡᵐ v +ⱽ h ·ˡᵐ v
    ; f[u+v]≡f[u]+f[v] = λ u v → +ˡᵐ-linearity g h u v u v
    ; f[c*v]≡c*f[v] = λ c v → +-homogeneity g h c v v
    }

  _-ˡᵐ_ : m ⊸ n → m ⊸ n → m ⊸ n
  g -ˡᵐ h = record
    { f = λ v → g ·ˡᵐ v -ⱽ h ·ˡᵐ v
    ; f[u+v]≡f[u]+f[v] = f[u+v]≡f[u]+f[v]' g h
    ; f[c*v]≡c*f[v] = f[c*v]≡c*f[v]' g h
    }
    where
      f[u+v]≡f[u]+f[v]' : (g h : m ⊸ n) → (u v : Vec A m)
                        → g ·ˡᵐ (u +ⱽ v) -ⱽ h ·ˡᵐ (u +ⱽ v) ≡
                           g ·ˡᵐ u -ⱽ h ·ˡᵐ u +ⱽ (g ·ˡᵐ v -ⱽ h ·ˡᵐ v)
      f[u+v]≡f[u]+f[v]' g h u v = begin
          g ·ˡᵐ (u +ⱽ v) -ⱽ h ·ˡᵐ (u +ⱽ v)
        ≡⟨ cong (g ·ˡᵐ (u +ⱽ v) +ⱽ_) (-ⱽ≡-1ᶠ∘ⱽ (h ·ˡᵐ (u +ⱽ v))) ⟩
          g ·ˡᵐ (u +ⱽ v) +ⱽ (- 1ᶠ) ∘ⱽ (h ·ˡᵐ (u +ⱽ v))
        ≡⟨ cong (λ x → g ·ˡᵐ (u +ⱽ v) +ⱽ (- 1ᶠ) ∘ⱽ x) (f[u+v]≡f[u]+f[v] h u v) ⟩
          g ·ˡᵐ (u +ⱽ v) +ⱽ (- 1ᶠ) ∘ⱽ (h ·ˡᵐ u +ⱽ h ·ˡᵐ v)
        ≡⟨ cong (g ·ˡᵐ (u +ⱽ v) +ⱽ_) (∘ⱽ-distr-+ⱽ (- 1ᶠ) (h ·ˡᵐ u) (h ·ˡᵐ v)) ⟩
          g ·ˡᵐ (u +ⱽ v) +ⱽ ((- 1ᶠ) ∘ⱽ h ·ˡᵐ u +ⱽ (- 1ᶠ) ∘ⱽ h ·ˡᵐ v)
        ≡⟨ cong₂ (λ x y → g ·ˡᵐ (u +ⱽ v) +ⱽ (x +ⱽ y))
                 (sym (f[c*v]≡c*f[v] h (- 1ᶠ) u))
                 (sym (f[c*v]≡c*f[v] h (- 1ᶠ) v)) ⟩
          g ·ˡᵐ (u +ⱽ v) +ⱽ (h ·ˡᵐ ((- 1ᶠ) ∘ⱽ u) +ⱽ h ·ˡᵐ ((- 1ᶠ) ∘ⱽ v))
        ≡⟨ cong (g ·ˡᵐ (u +ⱽ v) +ⱽ_)
                (sym (f[u+v]≡f[u]+f[v] h ((- 1ᶠ) ∘ⱽ u) ((- 1ᶠ) ∘ⱽ v))) ⟩
          g ·ˡᵐ (u +ⱽ v) +ⱽ (h ·ˡᵐ ((- 1ᶠ) ∘ⱽ u +ⱽ (- 1ᶠ) ∘ⱽ v))
        ≡⟨ +ˡᵐ-linearity g h u v ((- 1ᶠ) ∘ⱽ u) ((- 1ᶠ) ∘ⱽ v) ⟩
          g ·ˡᵐ u +ⱽ h ·ˡᵐ ((- 1ᶠ) ∘ⱽ u) +ⱽ (g ·ˡᵐ v +ⱽ h ·ˡᵐ ((- 1ᶠ) ∘ⱽ v))
        ≡⟨ cong₂ (λ x y → g ·ˡᵐ u +ⱽ x +ⱽ (g ·ˡᵐ v +ⱽ y))
          (trans (f[c*v]≡c*f[v] h ((- 1ᶠ)) u) (sym (-ⱽ≡-1ᶠ∘ⱽ (h ·ˡᵐ u))))
          (trans (f[c*v]≡c*f[v] h ((- 1ᶠ)) v) (sym (-ⱽ≡-1ᶠ∘ⱽ (h ·ˡᵐ v)))) ⟩
          g ·ˡᵐ u -ⱽ h ·ˡᵐ u +ⱽ (g ·ˡᵐ v -ⱽ h ·ˡᵐ v)
        ∎

      f[c*v]≡c*f[v]' : (g h : m ⊸ n) → (c : A) (v : Vec A m)
                     → g ·ˡᵐ (c ∘ⱽ v) -ⱽ h ·ˡᵐ (c ∘ⱽ v) ≡
                        c ∘ⱽ (g ·ˡᵐ v -ⱽ h ·ˡᵐ v)
      f[c*v]≡c*f[v]' g h c v = begin
          g ·ˡᵐ (c ∘ⱽ v) -ⱽ h ·ˡᵐ (c ∘ⱽ v)
        ≡⟨ cong (g ·ˡᵐ (c ∘ⱽ v) +ⱽ_)
          (trans (-ⱽ≡-1ᶠ∘ⱽ (h ·ˡᵐ (c ∘ⱽ v)))
                 (sym (f[c*v]≡c*f[v] h (- 1ᶠ) (c ∘ⱽ v)))) ⟩
          g ·ˡᵐ (c ∘ⱽ v) +ⱽ h ·ˡᵐ ((- 1ᶠ) ∘ⱽ (c ∘ⱽ v))
        ≡⟨ cong (λ x → g ·ˡᵐ (c ∘ⱽ v) +ⱽ h ·ˡᵐ x) (∘ⱽ-comm (- 1ᶠ) c v) ⟩
          g ·ˡᵐ (c ∘ⱽ v) +ⱽ h ·ˡᵐ (c ∘ⱽ ((- 1ᶠ) ∘ⱽ v))
        ≡⟨ +-homogeneity g h c v ((- 1ᶠ) ∘ⱽ v) ⟩
          c ∘ⱽ (g ·ˡᵐ v +ⱽ h ·ˡᵐ ((- 1ᶠ) ∘ⱽ v))
        ≡⟨ cong (λ x → c ∘ⱽ (g ·ˡᵐ v +ⱽ x))
                (trans (f[c*v]≡c*f[v] h (- 1ᶠ) v) (sym (-ⱽ≡-1ᶠ∘ⱽ (h ·ˡᵐ v)))) ⟩
          c ∘ⱽ (g ·ˡᵐ v -ⱽ h ·ˡᵐ v)
        ∎

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
                     → g ·ˡᵐ (h ·ˡᵐ (c ∘ⱽ v)) ≡ c ∘ⱽ g ·ˡᵐ (h ·ˡᵐ v)
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
                     → T ·ˡᵐ (c ∘ⱽ v) ++ B ·ˡᵐ (c ∘ⱽ v) ≡
                        c ∘ⱽ (T ·ˡᵐ v ++ B ·ˡᵐ v)
      f[c*v]≡c*f[v]' T B c v rewrite
          f[c*v]≡c*f[v] T c v
        | f[c*v]≡c*f[v] B c v
        | ∘ⱽ-distr-++ c (T ·ˡᵐ v) (B ·ˡᵐ v)
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
                       → T ·ˡᵐ take m (c ∘ⱽ v) +ⱽ B ·ˡᵐ drop m (c ∘ⱽ v) ≡
                          c ∘ⱽ (T ·ˡᵐ take m v +ⱽ B ·ˡᵐ drop m v)
        f[c*v]≡c*f[v]' {m} T B c v = begin
            T ·ˡᵐ take m (c ∘ⱽ v) +ⱽ B ·ˡᵐ drop m (c ∘ⱽ v)
          ≡⟨ cong₂ (λ x y → T ·ˡᵐ x +ⱽ B ·ˡᵐ y) (take-distr-map (c *_) m v)
                                                 (drop-distr-map (c *_) m v) ⟩
            T ·ˡᵐ (c ∘ⱽ take m v) +ⱽ B ·ˡᵐ (c ∘ⱽ drop m v)
          ≡⟨ cong₂ _+ⱽ_ (f[c*v]≡c*f[v] T c (take m v))
                        (f[c*v]≡c*f[v] B c (drop m v)) ⟩
            c ∘ⱽ (T ·ˡᵐ take m v) +ⱽ c ∘ⱽ (B ·ˡᵐ drop m v)
          ≡⟨ sym (∘ⱽ-distr-+ⱽ c (T ·ˡᵐ take m v) (B ·ˡᵐ drop m v)) ⟩
            c ∘ⱽ (T ·ˡᵐ take m v +ⱽ B ·ˡᵐ drop m v)
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
                       → T ·ˡᵐ (take m (c ∘ⱽ v)) ++ B ·ˡᵐ (drop m (c ∘ⱽ v)) ≡
                          c ∘ⱽ (T ·ˡᵐ (take m v) ++ B ·ˡᵐ (drop m v))
        f[c*v]≡c*f[v]' {m} T B c v =
          begin
              T ·ˡᵐ take m (c ∘ⱽ v) ++ B ·ˡᵐ drop m (c ∘ⱽ v)
            ≡⟨ cong₂ (λ x y → T ·ˡᵐ x ++ B ·ˡᵐ y) (take-distr-map (c *_) m v)
                                                   (drop-distr-map (c *_) m v) ⟩
              T ·ˡᵐ (c ∘ⱽ take m v) ++ B ·ˡᵐ (c ∘ⱽ (drop m v))
            ≡⟨ cong₂ _++_ (f[c*v]≡c*f[v] T c (take m v))
                          (f[c*v]≡c*f[v] B c (drop m v)) ⟩
              c ∘ⱽ (T ·ˡᵐ take m v) ++ c ∘ⱽ (B ·ˡᵐ drop m v)
            ≡⟨ sym (∘ⱽ-distr-++ c (T ·ˡᵐ take m v) (B ·ˡᵐ drop m v)) ⟩
              c ∘ⱽ (T ·ˡᵐ take m v ++ B ·ˡᵐ drop m v)
          ∎

  -- Multiply by a constant
  _∘ˡᵐ_ : A → n ⊸ m → n ⊸ m
  c ∘ˡᵐ m =
    record
      { f = λ v → c ∘ⱽ m ·ˡᵐ v
      ; f[u+v]≡f[u]+f[v] = λ u v → trans (cong (c ∘ⱽ_) (f[u+v]≡f[u]+f[v] m u v))
                                         (∘ⱽ-distr-+ⱽ c (m ·ˡᵐ u) (m ·ˡᵐ v))
      ; f[c*v]≡c*f[v] = λ c₁ v → trans (cong (c ∘ⱽ_) (f[c*v]≡c*f[v] m c₁ v))
                                       (∘ⱽ-comm c c₁ (f m v))
      }

  -- Choose 20 since function application is assumed higher than almost anything
  infixr 20 _·ˡᵐ_

  infixl 2 _—ˡᵐ_
  infixl 3 _|ˡᵐ_
  infixl 4 _/ˡᵐ_
  infixl 6 _+ˡᵐ_
  infixl 6 _-ˡᵐ_
  infixl 7 _*ˡᵐ_
  infixl 10 _∘ˡᵐ_


-- Example LinearMap values ---------------------------------------------------

module _ ⦃ F : Field A ⦄ where
  open Field F

  idₗₘ : n ⊸ n
  idₗₘ = record
    { f = id
    ; f[u+v]≡f[u]+f[v] = λ u v → refl
    ; f[c*v]≡c*f[v] = λ c v → refl
    }

  diagₗₘ : Vec A n → n ⊸ n
  diagₗₘ d = record
    { f = d *ⱽ_
    ; f[u+v]≡f[u]+f[v] = *ⱽ-distr-+ⱽ d
    ; f[c*v]≡c*f[v] = λ c v → *ⱽ∘ⱽ≡∘ⱽ*ⱽ c d v
    }

  allonesₗₘ : n ⊸ m
  allonesₗₘ = record
    { f = λ v → replicate (sum v)
    ; f[u+v]≡f[u]+f[v] = f[u+v]≡f[u]+f[v]
    ; f[c*v]≡c*f[v] = f[c*v]≡c*f[v]
    }
    where
      f[u+v]≡f[u]+f[v] : (u v : Vec A n)
                       → replicate (sum (u +ⱽ v)) ≡
                          replicate (sum u) +ⱽ replicate (sum v)
      f[u+v]≡f[u]+f[v] u v = begin
        replicate (sum (u +ⱽ v))      ≡⟨ cong replicate (sum-distr-+ⱽ u v) ⟩
        replicate ((sum u) + (sum v)) ≡⟨ replicate-distr-+ (sum u) (sum v) ⟩
        replicate (sum u) +ⱽ replicate (sum v) ∎

      f[c*v]≡c*f[v] : (c : A) (v : Vec A n)
                    → replicate (sum (c ∘ⱽ v)) ≡ c ∘ⱽ replicate (sum v)
      f[c*v]≡c*f[v] c v = begin
        replicate (sum (c ∘ⱽ v)) ≡⟨ cong replicate (sum[c∘ⱽv]≡c*sum[v] c v) ⟩
        replicate (c * sum v)    ≡⟨ replicate[a*b]≡a∘ⱽreplicate[b] c (sum v) ⟩
        c ∘ⱽ replicate (sum v)   ∎

  -- This could be defined as 0ᶠ ∘ˡᵐ allonesₗₘ, but then that would make
  -- some later proofs more difficult, since they would then have more than
  -- just replicate 0ᶠ to replace zerosₗₘ with.
  zerosₗₘ : n ⊸ m
  zerosₗₘ =  record
    { f = λ v → replicate 0ᶠ
    ; f[u+v]≡f[u]+f[v] = λ u v → sym (trans (zipWith-replicate _+_ 0ᶠ 0ᶠ)
                                             (cong replicate 0ᶠ+0ᶠ≡0ᶠ))
    ; f[c*v]≡c*f[v] = λ c v → sym (c∘ⱽ0ᶠⱽ≡0ᶠⱽ c)
    }
