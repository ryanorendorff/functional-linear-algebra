{-# OPTIONS --with-K #-}

open import Axiom.UniquenessOfIdentityProofs.WithK using (uip)

open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open ≡-Reasoning

open import Level using (Level)
open import Data.Nat using (ℕ)

open import Data.Vec using (Vec)

open import FLA.Axiom.Extensionality.Propositional
open import FLA.Algebra.Structures
open import FLA.Algebra.Properties.Field
open import FLA.Algebra.LinearMap
open import FLA.Algebra.LinearAlgebra
open import FLA.Algebra.LinearAlgebra.Matrix

module FLA.Algebra.LinearAlgebra.Properties.Matrix where

open MProperties

private
  variable
    ℓ : Level
    A : Set ℓ
    m n p q : ℕ
    ⦃ F ⦄ : Field A

-------------------------------------------------------------------------------
--                   M without the inner product proof: M↓                   --
-------------------------------------------------------------------------------

data M↓_∶_×_ (A : Set ℓ) ⦃ F : Field A ⦄ (m n : ℕ) : Set ℓ where
  ⟦_,_⟧ : (M : LinearMap A n m ) → (Mᵀ : LinearMap A m n ) → M↓ A ∶ m × n

_·↓_ : ⦃ F : Field A ⦄ → M↓ A ∶ m × n → Vec A n → Vec A m
⟦ f , a ⟧ ·↓ x = f ·ˡᵐ x

_ᵀ↓ : ⦃ F : Field A ⦄ → M↓ A ∶ m × n → M↓ A ∶ n × m
⟦ f , a ⟧ ᵀ↓ = ⟦ a , f ⟧

infixr 20 _·↓_
infixl 25 _ᵀ↓

M→M↓ : ⦃ F : Field A ⦄ → M A ∶ m × n → M↓ A ∶ m × n
M→M↓ ⟦ M , Mᵀ , p ⟧ = ⟦ M , Mᵀ ⟧

M↓→M : ⦃ F : Field A ⦄
      → (M↓ : M↓ A ∶ m × n)
      → (p : (x : Vec A m) → (y : Vec A n)
            → ⟨ x , M↓ ·↓ y ⟩ ≡ ⟨ y , M↓ ᵀ↓ ·↓ x ⟩ )
      → M A ∶ m × n
M↓→M ⟦ M , Mᵀ ⟧ p = ⟦ M , Mᵀ , p ⟧

⟨x,Ay⟩≡⟨y,Aᵀx⟩-UIP : {ℓ : Level} → {A : Set ℓ} → ⦃ F : Field A ⦄
                   → (C : LinearMap A n m) → (Cᵀ : LinearMap A m n)
                   → (p q : (x : Vec A m) (y : Vec A n)
                           → ⟨ x , C ·ˡᵐ y ⟩ ≡ ⟨ y , Cᵀ ·ˡᵐ x ⟩)
                   → p ≡ q
⟨x,Ay⟩≡⟨y,Aᵀx⟩-UIP {m} {n} {ℓ} {A} C Cᵀ p q =
  extensionality (λ x → extensionality (λ y → f C Cᵀ p q x y))
  where
    f : {m n : ℕ}
          → {A : Set ℓ}
          → ⦃ F : Field A ⦄
          → (C : LinearMap A n m) → (Cᵀ : LinearMap A m n)
          → (p q : (x : Vec A m) (y : Vec A n)
                  → ⟨ x , C ·ˡᵐ y ⟩ ≡ ⟨ y , Cᵀ ·ˡᵐ x ⟩)
          → (x : Vec A m) →  (y : Vec A n) → p x y ≡ q x y
    f C Cᵀ p q (x) (y) = uip (p x y) (q x y)

M↓≡→M≡ : ⦃ F : Field A ⦄ → (C D : M A ∶ m × n) → (M→M↓ C ≡ M→M↓ D) → C ≡ D
M↓≡→M≡ ⟦ C , Cᵀ , p ⟧ ⟦ .C , .Cᵀ , q ⟧ refl rewrite
  ⟨x,Ay⟩≡⟨y,Aᵀx⟩-UIP C Cᵀ p q = refl


-------------------------------------------------------------------------------
--                                Proofs on M                                --
-------------------------------------------------------------------------------

ᵀᵀ : {A : Set} ⦃ F : Field A ⦄ → (B : M A ∶ m × n) → B ᵀ ᵀ ≡ B
ᵀᵀ B = M↓≡→M≡ (B ᵀ ᵀ) B (ᵀᵀ↓ B)
  where
    ᵀᵀ↓ : {A : Set} ⦃ F : Field A ⦄ → (B : M A ∶ m × n) → M→M↓ (B ᵀ ᵀ) ≡ M→M↓ B
    ᵀᵀ↓ ⟦ M , Mᵀ , p ⟧ = refl

ᵀ-distr-* : {A : Set} ⦃ F : Field A ⦄ → (L : M A ∶ m × n) (R : M A ∶ n × p)
          → (L *ᴹ R) ᵀ ≡ (R ᵀ *ᴹ L ᵀ)
ᵀ-distr-* L R = M↓≡→M≡ ((L *ᴹ R) ᵀ) (R ᵀ *ᴹ L ᵀ) (ᵀ-distr-*↓ L R)
  where
    ᵀ-distr-*↓ : {A : Set} ⦃ F : Field A ⦄ → (L : M A ∶ m × n) (R : M A ∶ n × p)
               → M→M↓ ((L *ᴹ R) ᵀ) ≡ M→M↓ (R ᵀ *ᴹ L ᵀ)
    ᵀ-distr-*↓ ⟦ L , Lᵀ , p ⟧ ⟦ R , Rᵀ₁ , q ⟧ = refl

ᵀ-distr-+ : {A : Set} ⦃ F : Field A ⦄ → (L R : M A ∶ m × n)
           → (L +ᴹ R) ᵀ ≡ L ᵀ +ᴹ R ᵀ
ᵀ-distr-+ L R = M↓≡→M≡ ((L +ᴹ R) ᵀ) (L ᵀ +ᴹ R ᵀ) (ᵀ-distr-+↓ L R)
  where
    ᵀ-distr-+↓ : {A : Set} ⦃ F : Field A ⦄ → (L R : M A ∶ m × n)
               → M→M↓ ((L +ᴹ R) ᵀ) ≡ M→M↓ (L ᵀ +ᴹ R ᵀ)
    ᵀ-distr-+↓ ⟦ L , Lᵀ , p ⟧ ⟦ R , Rᵀ , q ⟧ = refl

-- Must prove the distribution proofs on LinearMap first.
-- *ᴹ-distr-+ᴹ↓ : {A : Set} ⦃ F : Field A ⦄
--              → (X : M A ∶ m × n) (Y Z : M A ∶ n × p)
--              → M→M↓ (X *ᴹ (Y +ᴹ Z)) ≡ M→M↓ (X *ᴹ Y +ᴹ X *ᴹ Z)
-- *ᴹ-distr-+ᴹ↓ ⟦ X , Xᵀ , Xₚ ⟧ ⟦ Y , Yᵀ , Yₚ ⟧ ⟦ Z , Zᵀ , Zₚ ⟧ = {!!}
-- rewrite *ˡᵐ-distr-+ˡᵐₗ X Y Z | *ˡᵐ-distr-+ˡᵐᵣ Yᵀ Zᵀ Xᵀ = refl
