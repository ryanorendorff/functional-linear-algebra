{-# OPTIONS --without-K --safe #-}

-- We do not parameterize this module since we do not have access to _+_ or _*_
-- for the fields that we want (real numbers)
open import Level using (Level)

open import Relation.Binary.PropositionalEquality hiding (∀-extensionality)
open ≡-Reasoning

open import Data.Nat using (ℕ; suc; zero)
open import Data.Vec using (Vec; foldr; zipWith; map)
                     renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)

open import FLA.Algebra.Structures
open import FLA.Algebra.Properties.Field
open import FLA.Algebra.LinearAlgebra
open import FLA.Algebra.LinearAlgebra.Properties

open import Function using (id)

module FLA.Algebra.LinearMap where

private
  variable
    ℓ : Level
    A : Set ℓ
    m n p q : ℕ
    ⦃ F ⦄ : Field A

record LinearMap (A : Set ℓ) ⦃ F : Field A ⦄ (m n : ℕ) : Set ℓ where
  field
    f : (Vec A m → Vec A n)

    -- Additivity
    f[u+v]≡f[u]+f[v] : (u v : Vec A m) → f (u +ⱽ v) ≡ f u +ⱽ f v

    -- Homogeneity
    f[c*v]≡c*f[v] : (c : A) → (v : Vec A m) → f (c *ᶜ v) ≡ c *ᶜ (f v)


_·ˡᵐ_ : ⦃ F : Field A ⦄ → LinearMap A m n → Vec A m → Vec A n
_·ˡᵐ_ LM = LinearMap.f LM

-- Choose 20 since function application is assumed higher than almost anything
infixr 20 _·ˡᵐ_


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

infixl 6 _+ˡᵐ_
infixl 7 _*ˡᵐ_


-------------------------------------------------------------------------------
--                           LinearMap constructor                           --
-------------------------------------------------------------------------------


-- If I can prove these two I can prove the distributive property on
-- matrices below.
-- +ˡᵐ-comm : ⦃ F : Field A ⦄ → (L R : LinearMap A m n)
--          → L +ˡᵐ R ≡ R +ˡᵐ L
-- +ˡᵐ-comm L R = {!!}

-- *ˡᵐ-distr-+ˡᵐₗ : ⦃ F : Field A ⦄
--                → (X : LinearMap A n m) → (Y Z : LinearMap A p n)
--                → X *ˡᵐ (Y +ˡᵐ Z) ≡ X *ˡᵐ Y +ˡᵐ X *ˡᵐ Z
-- *ˡᵐ-distr-+ˡᵐₗ X Y Z = {!!}

-- *ˡᵐ-distr-+ˡᵐᵣ : ⦃ F : Field A ⦄
--                → (X Y : LinearMap A n m) → (Z : LinearMap A p n)
--                → (X +ˡᵐ Y) *ˡᵐ Z ≡ X *ˡᵐ Z +ˡᵐ Y *ˡᵐ Z
-- *ˡᵐ-distr-+ˡᵐᵣ X Y Z = {!!}

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
