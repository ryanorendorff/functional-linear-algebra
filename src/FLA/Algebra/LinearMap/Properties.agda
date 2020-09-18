{-# OPTIONS --with-K #-}

open import Level using (Level)

open import Axiom.UniquenessOfIdentityProofs.WithK using (uip)

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec)

open import FLA.Axiom.Extensionality.Propositional
open import FLA.Algebra.Structures
open import FLA.Algebra.LinearAlgebra
open import FLA.Algebra.LinearAlgebra.Properties
open import FLA.Algebra.LinearMap

module FLA.Algebra.LinearMap.Properties where

private
  variable
    ℓ : Level
    A : Set ℓ
    m n p q : ℕ
    ⦃ F ⦄ : Field A

-------------------------------------------------------------------------------
--                  LinearMap without the proofs: LinearMap↓                 --
-------------------------------------------------------------------------------

private
  data _⊸↓_ {A : Set ℓ} ⦃ F : Field A ⦄ (m n : ℕ) : Set ℓ where
    LM↓ : (Vec A m → Vec A n) → m ⊸↓ n

  _·ˡᵐ↓_ : ⦃ F : Field A ⦄ → m ⊸↓ n → Vec A m → Vec A n
  _·ˡᵐ↓_ (LM↓ f) = f

  -- Choose 20 since function application is assumed higher than almost anything
  infixr 20 _·ˡᵐ↓_

  L→L↓ : ⦃ F : Field A ⦄ → m ⊸ n → m ⊸↓ n
  L→L↓ record { f = f } = LM↓ f

  L↓→L : ⦃ F : Field A ⦄
        → (L↓ : m ⊸↓ n)
        → (f[u+v]≡f[u]+f[v] : (u v : Vec A m)
                             → L↓ ·ˡᵐ↓ (u +ⱽ v) ≡ L↓ ·ˡᵐ↓ u +ⱽ L↓ ·ˡᵐ↓ v)
        → (f[c*v]≡c*f[v] : (c : A) → (v : Vec A m)
                          → L↓ ·ˡᵐ↓ (c ∘ⱽ v) ≡ c ∘ⱽ (L↓ ·ˡᵐ↓ v))
        → m ⊸ n
  L↓→L (LM↓ f) f[u+v]≡f[u]+f[v] f[c*v]≡c*f[v] =
    record
      { f = f
      ; f[u+v]≡f[u]+f[v] = f[u+v]≡f[u]+f[v]
      ; f[c*v]≡c*f[v] = f[c*v]≡c*f[v]
      }

  f[u+v]≡f[u]+f[v]-UIP : {ℓ : Level} {A : Set ℓ} {m n : ℕ} → ⦃ F : Field A ⦄
    → (f : Vec A m → Vec A n)
    → (p q : (u v : Vec A m)
            → f (u +ⱽ v) ≡ f u +ⱽ f v)
    → p ≡ q
  f[u+v]≡f[u]+f[v]-UIP f p q =
    extensionality (λ u → extensionality (λ v → t f p q u v))
    where
      t : {ℓ : Level} {A : Set ℓ} {m n : ℕ} → ⦃ F : Field A ⦄
        → (f : Vec A m → Vec A n)
        → (p q : (u v : Vec A m)
                → f (u +ⱽ v) ≡ f u +ⱽ f v)
        → (u v : Vec A m) → p u v ≡ q u v
      t f p q u v = uip (p u v) (q u v)

  f[c*v]≡c*f[v]-UIP : {ℓ : Level} {A : Set ℓ} {m n : ℕ} → ⦃ F : Field A ⦄
                    → (f : Vec A m → Vec A n)
                    → (p q : (c : A) (v : Vec A m) → f (c ∘ⱽ v) ≡ c ∘ⱽ (f v))
                    → p ≡ q
  f[c*v]≡c*f[v]-UIP f p q =
    extensionality (λ c → extensionality (λ v → t f p q c v))
    where
      t : {ℓ : Level} {A : Set ℓ} {m n : ℕ} → ⦃ F : Field A ⦄
        → (f : Vec A m → Vec A n)
        → (p q : (c : A) (v : Vec A m) → f (c ∘ⱽ v) ≡ c ∘ⱽ (f v))
        → (c : A) (v : Vec A m) → p c v ≡ q c v
      t f p q c v = uip (p c v) (q c v)

  L↓≡→L≡ : ⦃ F : Field A ⦄ → (C D : m ⊸ n)
          → (L→L↓ C ≡ L→L↓ D) → C ≡ D
  L↓≡→L≡ record { f = f
                 ; f[u+v]≡f[u]+f[v] = f[u+v]≡f[u]+f[v]ᶜ
                 ; f[c*v]≡c*f[v] = f[c*v]≡c*f[v]ᶜ
                 }
          record { f = .f
                 ; f[u+v]≡f[u]+f[v] = f[u+v]≡f[u]+f[v]ᵈ
                 ; f[c*v]≡c*f[v] = f[c*v]≡c*f[v]ᵈ
                 }
          refl
    rewrite
      f[u+v]≡f[u]+f[v]-UIP f f[u+v]≡f[u]+f[v]ᶜ f[u+v]≡f[u]+f[v]ᵈ
    | f[c*v]≡c*f[v]-UIP f f[c*v]≡c*f[v]ᶜ f[c*v]≡c*f[v]ᵈ
    = refl


-------------------------------------------------------------------------------
--                   LinearMap Proofs via LinearMap↓ Proofs                  --
-------------------------------------------------------------------------------

module _ {ℓ : Level} {A : Set ℓ} ⦃ F : Field A ⦄ where
  open Field F
  open _⊸_

  +ˡᵐ-comm : (L R : m ⊸ n)
          → L +ˡᵐ R ≡ R +ˡᵐ L
  +ˡᵐ-comm L R = L↓≡→L≡ (L +ˡᵐ R) (R +ˡᵐ L) (+ˡᵐ-comm↓ L R)
    where
      +ⱽ-comm-ext : (f g : Vec A m → Vec A n)
        → (λ v → f v +ⱽ g v) ≡ (λ v → g v +ⱽ f v)
      +ⱽ-comm-ext f g = extensionality (λ v → +ⱽ-comm (f v) (g v))

      +ˡᵐ-comm↓ : (L R : m ⊸ n)
              → L→L↓ (L +ˡᵐ R) ≡ L→L↓ (R +ˡᵐ L)
      +ˡᵐ-comm↓ L R = cong LM↓ (+ⱽ-comm-ext (L ·ˡᵐ_) (R ·ˡᵐ_))

  *ˡᵐ-distr-+ˡᵐₗ : (X : n ⊸ m) → (Y Z : p ⊸ n)
                → (X *ˡᵐ (Y +ˡᵐ Z)) ≡ (X *ˡᵐ Y +ˡᵐ X *ˡᵐ Z)
  *ˡᵐ-distr-+ˡᵐₗ X Y Z = L↓≡→L≡ (X *ˡᵐ (Y +ˡᵐ Z)) ((X *ˡᵐ Y +ˡᵐ X *ˡᵐ Z))
                                (*ˡᵐ-distr-+ˡᵐₗ↓ X Y Z)
    where
      *-distr-+ⱽ : (X : n ⊸ m) → (Y Z : p ⊸ n)
        → (λ v → X ·ˡᵐ (Y ·ˡᵐ v +ⱽ Z ·ˡᵐ v)) ≡
          (λ v → X ·ˡᵐ (Y ·ˡᵐ v) +ⱽ X ·ˡᵐ (Z ·ˡᵐ v))
      *-distr-+ⱽ X Y Z = extensionality
        (λ v → f[u+v]≡f[u]+f[v] X (Y ·ˡᵐ v) (Z ·ˡᵐ v))

      *ˡᵐ-distr-+ˡᵐₗ↓ : (X : n ⊸ m) → (Y Z : p ⊸ n)
                      → L→L↓ (X *ˡᵐ (Y +ˡᵐ Z)) ≡ L→L↓ (X *ˡᵐ Y +ˡᵐ X *ˡᵐ Z)
      *ˡᵐ-distr-+ˡᵐₗ↓ X Y Z = cong LM↓ (*-distr-+ⱽ X Y Z)

  *ˡᵐ-distr-+ˡᵐᵣ : (X Y : n ⊸ m) → (Z : p ⊸ n)
                → (X +ˡᵐ Y) *ˡᵐ Z ≡ X *ˡᵐ Z +ˡᵐ Y *ˡᵐ Z
  *ˡᵐ-distr-+ˡᵐᵣ X Y Z = L↓≡→L≡ ((X +ˡᵐ Y) *ˡᵐ Z) (X *ˡᵐ Z +ˡᵐ Y *ˡᵐ Z)
                                (*ˡᵐ-distr-+ˡᵐᵣ↓ X Y Z)
    where
      *ˡᵐ-distr-+ˡᵐᵣ↓ : (X Y : n ⊸ m) → (Z : p ⊸ n)
                      → L→L↓ ((X +ˡᵐ Y) *ˡᵐ Z) ≡ L→L↓ (X *ˡᵐ Z +ˡᵐ Y *ˡᵐ Z)
      *ˡᵐ-distr-+ˡᵐᵣ↓ X Y Z = cong LM↓ refl
