{-# OPTIONS --with-K #-}

open import Axiom.UniquenessOfIdentityProofs.WithK using (uip)

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Level using (Level)
open import Data.Nat using (ℕ)

open import Data.Vec using (Vec)

open import FLA.Axiom.Extensionality.Propositional
open import FLA.Algebra.Structures
open import FLA.Algebra.Properties.Field
open import FLA.Algebra.LinearMap
open import FLA.Algebra.LinearMap.Properties
open import FLA.Algebra.LinearAlgebra
open import FLA.Algebra.LinearAlgebra.Matrix

module FLA.Algebra.LinearAlgebra.Properties.Matrix where

private
  variable
    ℓ : Level
    A : Set ℓ
    m n p q : ℕ
    ⦃ F ⦄ : Field A


-------------------------------------------------------------------------------
--                   M without the inner product proof: Mat↓                   --
-------------------------------------------------------------------------------

private
  data Mat↓_∶_×_ (A : Set ℓ) ⦃ F : Field A ⦄ (m n : ℕ) : Set ℓ where
    ⟦_,_⟧ : (M : n ⊸ m ) → (Mᵀ : m ⊸ n ) → Mat↓ A ∶ m × n

  _·↓_ : ⦃ F : Field A ⦄ → Mat↓ A ∶ m × n → Vec A n → Vec A m
  ⟦ f , a ⟧ ·↓ x = f ·ˡᵐ x

  _ᵀ↓ : ⦃ F : Field A ⦄ → Mat↓ A ∶ m × n → Mat↓ A ∶ n × m
  ⟦ f , a ⟧ ᵀ↓ = ⟦ a , f ⟧

  infixr 20 _·↓_
  infixl 25 _ᵀ↓

  Mat→Mat↓ : ⦃ F : Field A ⦄ → Mat m × n → Mat↓ A ∶ m × n
  Mat→Mat↓ ⟦ M , Mᵀ , p ⟧ = ⟦ M , Mᵀ ⟧

  Mat↓→Mat : ⦃ F : Field A ⦄
        → (Mat↓ : Mat↓ A ∶ m × n)
        → (p : (x : Vec A m) → (y : Vec A n)
              → ⟨ x , Mat↓ ·↓ y ⟩ ≡ ⟨ y , Mat↓ ᵀ↓ ·↓ x ⟩ )
        → Mat m × n
  Mat↓→Mat ⟦ M , Mᵀ ⟧ p = ⟦ M , Mᵀ , p ⟧

  ⟨x,Ay⟩≡⟨y,Aᵀx⟩-UIP : {ℓ : Level} → {A : Set ℓ} → ⦃ F : Field A ⦄
                    → (C : n ⊸ m) → (Cᵀ : m ⊸ n)
                    → (p q : (x : Vec A m) (y : Vec A n)
                            → ⟨ x , C ·ˡᵐ y ⟩ ≡ ⟨ y , Cᵀ ·ˡᵐ x ⟩)
                    → p ≡ q
  ⟨x,Ay⟩≡⟨y,Aᵀx⟩-UIP {m} {n} {ℓ} {A} C Cᵀ p q =
    extensionality (λ x → extensionality (λ y → f C Cᵀ p q x y))
    where
      f : {m n : ℕ}
            → {A : Set ℓ}
            → ⦃ F : Field A ⦄
            → (C : n ⊸ m) → (Cᵀ : m ⊸ n)
            → (p q : (x : Vec A m) (y : Vec A n)
                    → ⟨ x , C ·ˡᵐ y ⟩ ≡ ⟨ y , Cᵀ ·ˡᵐ x ⟩)
            → (x : Vec A m) →  (y : Vec A n) → p x y ≡ q x y
      f C Cᵀ p q (x) (y) = uip (p x y) (q x y)

  Mat↓≡→Mat≡ : ⦃ F : Field A ⦄ → (C D : Mat m × n) → (Mat→Mat↓ C ≡ Mat→Mat↓ D) → C ≡ D
  Mat↓≡→Mat≡ ⟦ C , Cᵀ , p ⟧ ⟦ .C , .Cᵀ , q ⟧ refl rewrite
    ⟨x,Ay⟩≡⟨y,Aᵀx⟩-UIP C Cᵀ p q = refl


-------------------------------------------------------------------------------
--                                Proofs on M                                --
-------------------------------------------------------------------------------

module _ {ℓ : Level} {A : Set ℓ} ⦃ F : Field A ⦄ where
  open Field F

  ᵀᵀ : (B : Mat m × n) → B ᵀ ᵀ ≡ B
  ᵀᵀ B = Mat↓≡→Mat≡ (B ᵀ ᵀ) B (ᵀᵀ↓ B)
    where
      ᵀᵀ↓ : (B : Mat m × n) → Mat→Mat↓ (B ᵀ ᵀ) ≡ Mat→Mat↓ B
      ᵀᵀ↓ ⟦ M , Mᵀ , p ⟧ = refl

  ᵀ-distr-* : (L : Mat m × n) (R : Mat n × p)
            → (L *ᴹ R) ᵀ ≡ (R ᵀ *ᴹ L ᵀ)
  ᵀ-distr-* L R = Mat↓≡→Mat≡ ((L *ᴹ R) ᵀ) (R ᵀ *ᴹ L ᵀ) (ᵀ-distr-*↓ L R)
    where
      ᵀ-distr-*↓ : (L : Mat m × n) (R : Mat n × p)
                → Mat→Mat↓ ((L *ᴹ R) ᵀ) ≡ Mat→Mat↓ (R ᵀ *ᴹ L ᵀ)
      ᵀ-distr-*↓ ⟦ L , Lᵀ , p ⟧ ⟦ R , Rᵀ₁ , q ⟧ = refl

  ᵀ-distr-+ : (L R : Mat m × n) → (L +ᴹ R) ᵀ ≡ L ᵀ +ᴹ R ᵀ
  ᵀ-distr-+ L R = Mat↓≡→Mat≡ ((L +ᴹ R) ᵀ) (L ᵀ +ᴹ R ᵀ) (ᵀ-distr-+↓ L R)
    where
      ᵀ-distr-+↓ : (L R : Mat m × n)
                 → Mat→Mat↓ ((L +ᴹ R) ᵀ) ≡ Mat→Mat↓ (L ᵀ +ᴹ R ᵀ)
      ᵀ-distr-+↓ ⟦ L , Lᵀ , p ⟧ ⟦ R , Rᵀ , q ⟧ = refl

  *ᴹ-distr-+ᴹₗ : (X : Mat m × n) (Y Z : Mat n × p)
               → X *ᴹ (Y +ᴹ Z) ≡ X *ᴹ Y +ᴹ X *ᴹ Z
  *ᴹ-distr-+ᴹₗ X Y Z = Mat↓≡→Mat≡ (X *ᴹ (Y +ᴹ Z)) (X *ᴹ Y +ᴹ X *ᴹ Z)
                              (*ᴹ-distr-+ᴹ↓ₗ X Y Z)
    where
      *ᴹ-distr-+ᴹ↓ₗ : (X : Mat m × n) (Y Z : Mat n × p)
                    → Mat→Mat↓ (X *ᴹ (Y +ᴹ Z)) ≡ Mat→Mat↓ (X *ᴹ Y +ᴹ X *ᴹ Z)
      *ᴹ-distr-+ᴹ↓ₗ ⟦ X , Xᵀ , Xₚ ⟧ ⟦ Y , Yᵀ , Yₚ ⟧ ⟦ Z , Zᵀ , Zₚ ⟧ rewrite
          *ˡᵐ-distr-+ˡᵐₗ X Y Z
        | *ˡᵐ-distr-+ˡᵐᵣ Yᵀ Zᵀ Xᵀ
        = refl

  *ᴹ-distr-+ᴹᵣ : (X Y : Mat m × n) (Z : Mat n × p)
               → (X +ᴹ Y) *ᴹ Z ≡ X *ᴹ Z +ᴹ Y *ᴹ Z
  *ᴹ-distr-+ᴹᵣ X Y Z = Mat↓≡→Mat≡ ((X +ᴹ Y) *ᴹ Z) (X *ᴹ Z +ᴹ Y *ᴹ Z)
                              (*ᴹ-distr-+ᴹ↓ᵣ X Y Z)
    where
      *ᴹ-distr-+ᴹ↓ᵣ : (X Y : Mat m × n) (Z : Mat n × p)
                    → Mat→Mat↓ ((X +ᴹ Y) *ᴹ Z) ≡ Mat→Mat↓ (X *ᴹ Z +ᴹ Y *ᴹ Z)
      *ᴹ-distr-+ᴹ↓ᵣ ⟦ X , Xᵀ , Xₚ ⟧ ⟦ Y , Yᵀ , Yₚ ⟧ ⟦ Z , Zᵀ , Zₚ ⟧ rewrite
          *ˡᵐ-distr-+ˡᵐᵣ X Y Z
        | *ˡᵐ-distr-+ˡᵐₗ Zᵀ Xᵀ Yᵀ
        = refl
