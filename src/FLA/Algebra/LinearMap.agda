{-# OPTIONS --without-K --safe #-}

-- We do not parameterize this module since we do not have access to _+_ or _*_
-- for the fields that we want (real numbers)
open import Level using (Level)

open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open ≡-Reasoning

open import Data.Nat using (ℕ; suc; zero) renaming (_+_ to _+ᴺ_)
open import Data.Nat.Properties
open import Data.Vec using (Vec; foldr; zipWith; map; _++_; []; _∷_)
open import Data.Vec.Properties

open import FLA.Algebra.Structures
open import FLA.Algebra.Properties.Field
open import FLA.Algebra.LinearAlgebra
open import FLA.Algebra.LinearAlgebra.Properties
open import FLA.Data.VectorList using (split)

open import Function using (id)

module FLA.Algebra.LinearMap where

private
  variable
    ℓ : Level
    A : Set ℓ
    m n p q : ℕ

record LinearMap (A : Set ℓ) ⦃ F : Field A ⦄ (m n : ℕ) : Set ℓ where
  field
    f : (Vec A m → Vec A n)

    -- Additivity
    f[u+v]≡f[u]+f[v] : (u v : Vec A m) → f (u +ⱽ v) ≡ f u +ⱽ f v

    -- Homogeneity
    f[c*v]≡c*f[v] : (c : A) → (v : Vec A m) → f (c *ᶜ v) ≡ c *ᶜ (f v)

_·ˡᵐ_ : ⦃ F : Field A ⦄ → LinearMap A m n → Vec A m → Vec A n
_·ˡᵐ_ LM = LinearMap.f LM

_+ˡᵐ_ : ⦃ F : Field A ⦄ → LinearMap A m n → LinearMap A m n → LinearMap A m n
g +ˡᵐ h = record
  { f = λ v → g ·ˡᵐ v +ⱽ h ·ˡᵐ v
  ; f[u+v]≡f[u]+f[v] = additivity g h
  ; f[c*v]≡c*f[v] = homogeneity g h
  }
  where open Field {{...}}
        additivity : ⦃ F : Field A ⦄
                   → (g h : LinearMap A m n)→ (u v : Vec A m)
                   → g ·ˡᵐ (u +ⱽ v) +ⱽ h ·ˡᵐ (u +ⱽ v) ≡
                      g ·ˡᵐ u +ⱽ h ·ˡᵐ u +ⱽ (g ·ˡᵐ v +ⱽ h ·ˡᵐ v)
        additivity g h u v rewrite
            LinearMap.f[u+v]≡f[u]+f[v] g u v
          | LinearMap.f[u+v]≡f[u]+f[v] h u v
          | (+ⱽ-assoc (g ·ˡᵐ u) (g ·ˡᵐ v) (h ·ˡᵐ u +ⱽ h ·ˡᵐ v))
          | sym (+ⱽ-assoc (g ·ˡᵐ v) (h ·ˡᵐ u) (h ·ˡᵐ v))
          | +ⱽ-comm (g ·ˡᵐ v) (h ·ˡᵐ u)
          | (+ⱽ-assoc (h ·ˡᵐ u) (g ·ˡᵐ v) (h ·ˡᵐ v))
          | sym (+ⱽ-assoc (g ·ˡᵐ u) (h ·ˡᵐ u) (g ·ˡᵐ v +ⱽ h ·ˡᵐ v))
          = refl

        homogeneity : ⦃ F : Field A ⦄
                    → (g h : LinearMap A m n) → (c : A) (v : Vec A m)
                    → g ·ˡᵐ (c *ᶜ v) +ⱽ h ·ˡᵐ (c *ᶜ v) ≡ c *ᶜ (g ·ˡᵐ v +ⱽ h ·ˡᵐ v)
        homogeneity g h c v rewrite
            LinearMap.f[c*v]≡c*f[v] g c v
          | LinearMap.f[c*v]≡c*f[v] h c v
          | sym (*ᶜ-distr-+ⱽ c (g ·ˡᵐ v) (h ·ˡᵐ v))
          = refl

_*ˡᵐ_ : ⦃ F : Field A ⦄ → LinearMap A n p → LinearMap A m n → LinearMap A m p
g *ˡᵐ h = record
  { f = λ v → g ·ˡᵐ (h ·ˡᵐ v)
  ; f[u+v]≡f[u]+f[v] = additivity g h
  ; f[c*v]≡c*f[v] = homogeneity g h
  }
  where open Field {{...}}
        additivity : ⦃ F : Field A ⦄
                   → (g : LinearMap A n p)
                   → (h : LinearMap A m n)
                   → (u v : Vec A m)
                   → g ·ˡᵐ (h ·ˡᵐ (u +ⱽ v)) ≡ g ·ˡᵐ (h ·ˡᵐ u) +ⱽ g ·ˡᵐ (h ·ˡᵐ v)
        additivity g h u v rewrite
            LinearMap.f[u+v]≡f[u]+f[v] h u v
          | LinearMap.f[u+v]≡f[u]+f[v] g (LinearMap.f h u) (LinearMap.f h v)
          = refl

        homogeneity : ⦃ F : Field A ⦄
                    → (g : LinearMap A n p)
                    → (h : LinearMap A m n)
                    → (c : A) (v : Vec A m)
                    → g ·ˡᵐ (h ·ˡᵐ (c *ᶜ v)) ≡ c *ᶜ g ·ˡᵐ (h ·ˡᵐ v)
        homogeneity g h c v rewrite
            LinearMap.f[c*v]≡c*f[v] h c v
          | LinearMap.f[c*v]≡c*f[v] g c (h ·ˡᵐ v)
          = refl

_|ˡᵐ_ : ⦃ F : Field A ⦄
      → LinearMap A p m → LinearMap A p n → LinearMap A p (m +ᴺ n)
T |ˡᵐ B =
  record
    { f = λ v →  T ·ˡᵐ v ++ B ·ˡᵐ v
    ; f[u+v]≡f[u]+f[v] = f[u+v]≡f[u]+f[v] T B
    ; f[c*v]≡c*f[v] = f[c*v]≡c*f[v] T B
    }
  where
    f[u+v]≡f[u]+f[v] : {A : Set ℓ} ⦃ F : Field A ⦄
                     → (T : LinearMap A p m) → (B : LinearMap A p n)
                     → (u v : Vec A p)
                     → T ·ˡᵐ (u +ⱽ v) ++ B ·ˡᵐ (u +ⱽ v) ≡
                       (T ·ˡᵐ u ++ B ·ˡᵐ u) +ⱽ (T ·ˡᵐ v ++ B ·ˡᵐ v)
    f[u+v]≡f[u]+f[v] T B u v rewrite
        LinearMap.f[u+v]≡f[u]+f[v] T u v
      | LinearMap.f[u+v]≡f[u]+f[v] B u v
      | +ⱽ-flip-++ (T ·ˡᵐ u) (T ·ˡᵐ v) (B ·ˡᵐ u) (B ·ˡᵐ v)
      = refl

    f[c*v]≡c*f[v] : {A : Set ℓ} ⦃ F : Field A ⦄
                  → (T : LinearMap A p m) → (B : LinearMap A p n)
                  → (c : A) → (v : Vec A p)
                  → T ·ˡᵐ (c *ᶜ v) ++ B ·ˡᵐ (c *ᶜ v) ≡
                     c *ᶜ (T ·ˡᵐ v ++ B ·ˡᵐ v)
    f[c*v]≡c*f[v] T B c v rewrite
        LinearMap.f[c*v]≡c*f[v] T c v
      | LinearMap.f[c*v]≡c*f[v] B c v
      | *ᶜ-distr-++ c (T ·ˡᵐ v) (B ·ˡᵐ v)
      = refl

-- _—ˡᵐ_ : ⦃ F : Field A ⦄
--       → LinearMap A m p → LinearMap A n p → LinearMap A (m +ᴺ n) p
-- _—ˡᵐ_ {ℓ} {A} {m} {n} {p} T B =
--   record
--     { f = λ v → T ·ˡᵐ (take m v) +ⱽ B ·ˡᵐ (drop m v)
--     ; f[u+v]≡f[u]+f[v] = {!f[u+v]≡f[u]+f[v] T B!}
--     ; f[c*v]≡c*f[v] = {!!}
--     }
--     where

infixl 3 _|ˡᵐ_
infixl 6 _+ˡᵐ_
infixl 7 _*ˡᵐ_
-- Choose 20 since function application is assumed higher than almost anything
infixr 20 _·ˡᵐ_


-- Example LinearMap values ---------------------------------------------------

idₗₘ : ⦃ F : Field A ⦄ → LinearMap A n n
idₗₘ = record
  { f = id
  ; f[u+v]≡f[u]+f[v] = λ u v → refl
  ; f[c*v]≡c*f[v] = λ c v → refl
  }

diagₗₘ : ⦃ F : Field A ⦄ → Vec A n → LinearMap A n n
diagₗₘ d = record
  { f = d ∘ⱽ_
  ; f[u+v]≡f[u]+f[v] = ∘ⱽ-distr-+ⱽ d
  ; f[c*v]≡c*f[v] = λ c v → ∘ⱽ*ᶜ≡*ᶜ∘ⱽ c d v
  }
