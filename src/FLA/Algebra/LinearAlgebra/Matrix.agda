{-# OPTIONS --with-K #-}

module FLA.Algebra.LinearAlgebra.Matrix where

open import Level using (Level)
open import Data.Nat using (ℕ; suc; zero)

open import Data.Empty

open import Data.Vec using (Vec; foldr; zipWith; map)
                     renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Product hiding (map; _,_)

open import Axiom.UniquenessOfIdentityProofs.WithK using (uip)
open import Relation.Binary.PropositionalEquality hiding (∀-extensionality)
open ≡-Reasoning

open import Function using (id)

open import FLA.Algebra.Structures
open import FLA.Algebra.Properties.Field
open import FLA.Algebra.LinearMap
open import FLA.Algebra.LinearAlgebra
open import FLA.Algebra.LinearAlgebra.Properties

private
  variable
    ℓ : Level
    A : Set ℓ
    m n p q : ℕ
    ⦃ F ⦄ : Field A


-------------------------------------------------------------------------------
--                          M constructor and values                         --
-------------------------------------------------------------------------------

data M_∶_×_ (A : Set ℓ) ⦃ F : Field A ⦄ (m n : ℕ) : Set ℓ where
  ⟦_,_,_⟧ : (M : LinearMap A n m )
          → (Mᵀ : LinearMap A m n )
          → (p : (x : Vec A m) → (y : Vec A n)
               → ⟨ x , M ·ˡᵐ y ⟩ ≡ ⟨ y , Mᵀ ·ˡᵐ x ⟩ )
          → M A ∶ m × n

_ᵀ : ⦃ F : Field A ⦄ → M A ∶ m × n → M A ∶ n × m
⟦ f , a , p ⟧ ᵀ = ⟦ a , f , (λ x y → sym (p y x)) ⟧

_·_ : ⦃ F : Field A ⦄ → M A ∶ m × n → Vec A n → Vec A m
⟦ f , a , _ ⟧ · x = f ·ˡᵐ x

module MProperties ⦃ F : Field A ⦄ where
  open Field F

  _+ᴹ_ : M A ∶ m × n → M A ∶ m × n → M A ∶ m × n
  ⟦ M₁ , M₁ᵀ , p₁ ⟧ +ᴹ ⟦ M₂ , M₂ᵀ , p₂ ⟧ =
    ⟦ M₁ +ˡᵐ M₂
    , M₁ᵀ +ˡᵐ M₂ᵀ
    , ⟨⟩-proof M₁ M₂ M₁ᵀ M₂ᵀ p₁ p₂
    ⟧
    where
      ⟨⟩-proof : (M₁ M₂ : LinearMap A n m)
               → (M₁ᵀ M₂ᵀ : LinearMap A m n)
               → (M₁-⟨⟩-proof : (x : Vec A m) (y : Vec A n)
                               → ⟨ x , M₁ ·ˡᵐ y ⟩ ≡ ⟨ y , M₁ᵀ ·ˡᵐ x ⟩ )
               → (M₂-⟨⟩-proof : (x : Vec A m) (y : Vec A n)
                               → ⟨ x , M₂ ·ˡᵐ y ⟩ ≡ ⟨ y , M₂ᵀ ·ˡᵐ x ⟩ )
               → (x : Vec A m) (y : Vec A n)
               → ⟨ x , (M₁ +ˡᵐ M₂) ·ˡᵐ y ⟩ ≡ ⟨ y , (M₁ᵀ +ˡᵐ M₂ᵀ) ·ˡᵐ x ⟩
      ⟨⟩-proof M₁ M₂ M₁ᵀ M₂ᵀ M₁-proof M₂-proof x y =
        begin
          ⟨ x , (M₁ +ˡᵐ M₂) ·ˡᵐ y ⟩             ≡⟨⟩
          ⟨ x , M₁ ·ˡᵐ y +ⱽ M₂ ·ˡᵐ y ⟩          ≡⟨ ⟨⟩-Properties.⟨x,y+z⟩≡⟨x,y⟩+⟨x,z⟩ x
                                                   (M₁ ·ˡᵐ y) (M₂ ·ˡᵐ y) ⟩
          ⟨ x , M₁ ·ˡᵐ y ⟩ + ⟨ x , M₂ ·ˡᵐ y ⟩   ≡⟨ cong (_+ ⟨ x , M₂ ·ˡᵐ y ⟩)
                                                        (M₁-proof x y) ⟩
          ⟨ y , M₁ᵀ ·ˡᵐ x ⟩ + ⟨ x , M₂ ·ˡᵐ y ⟩  ≡⟨ cong (⟨ y , M₁ᵀ ·ˡᵐ x ⟩ +_)
                                                        (M₂-proof x y) ⟩
          ⟨ y , M₁ᵀ ·ˡᵐ x ⟩ + ⟨ y , M₂ᵀ ·ˡᵐ x ⟩ ≡⟨ sym (⟨⟩-Properties.⟨x,y+z⟩≡⟨x,y⟩+⟨x,z⟩ y
                                                   (M₁ᵀ ·ˡᵐ x) (M₂ᵀ ·ˡᵐ x)) ⟩
          ⟨ y , (M₁ᵀ +ˡᵐ M₂ᵀ) ·ˡᵐ x ⟩           ∎

  _*ᴹ_ : M A ∶ m × n → M A ∶ n × p → M A ∶ m × p
  ⟦ M₁ , M₁ᵀ , p₁ ⟧ *ᴹ ⟦ M₂ , M₂ᵀ , p₂ ⟧ =
    ⟦ M₁ *ˡᵐ M₂
    , M₂ᵀ *ˡᵐ M₁ᵀ
    , ⟨⟩-proof M₁ M₂ M₁ᵀ M₂ᵀ p₁ p₂
    ⟧
    where
      ⟨⟩-proof : (M₁ : LinearMap A n m) (M₂ : LinearMap A p n)
               → (M₁ᵀ : LinearMap A m n) (M₂ᵀ : LinearMap A n p)
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

  infixl 6 _+ᴹ_
  infixl 7 _*ᴹ_

open MProperties

infixr 20 _·_
infixl 25 _ᵀ


-- Matrix Free Operators ------------------------------------------------------

I : ⦃ F : Field A ⦄ → M A ∶ n × n
I = ⟦ idₗₘ , idₗₘ , id-transpose  ⟧
  where
    id-transpose : ⦃ F : Field A ⦄ → (x y : Vec A n)
                 → ⟨ x , id y ⟩ ≡ ⟨ y , id x ⟩
    id-transpose {{F}} x y rewrite
        zipWith-comm (Field._*_ F) (Field.*-comm F) x y
      = refl


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


postulate
  extensionality : ∀ {A B : Set ℓ} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

part₁ :
  ⦃ F : Field A ⦄ →
  (C : LinearMap A n m) → (Cᵀ : LinearMap A m n) →
  (p q : (x : Vec A m) (y : Vec A n) → ⟨ x , C ·ˡᵐ y ⟩ ≡ ⟨ y , Cᵀ ·ˡᵐ x ⟩) →
  (x : Vec A m) →  (y : Vec A n) → p x y ≡ q x y
part₁ C Cᵀ p q (x) (y) = uip (p x y) (q x y)

postulate
  ⟨x,Ay⟩≡⟨y,Aᵀx⟩-UIP : {ℓ : Level} → {A : Set ℓ} → ⦃ F : Field A ⦄
                     → (C : LinearMap A n m) → (Cᵀ : LinearMap A m n)
                     → (p q : (x : Vec A m) (y : Vec A n)
                             → ⟨ x , C ·ˡᵐ y ⟩ ≡ ⟨ y , Cᵀ ·ˡᵐ x ⟩)
                     → p ≡ q
-- ⟨x,Ay⟩≡⟨y,Aᵀx⟩-UIP : {ℓ : Level} → {A : Set ℓ} → ⦃ F : Field A ⦄
--                    → (C : LinearMap A n m) → (Cᵀ : LinearMap A m n)
--                    → (p q : (x : Vec A m) (y : Vec A n)
--                            → ⟨ x , C ·ˡᵐ y ⟩ ≡ ⟨ y , Cᵀ ·ˡᵐ x ⟩)
--                    → p ≡ q
-- ⟨x,Ay⟩≡⟨y,Aᵀx⟩-UIP {n} {m} {ℓ} {A} C Cᵀ p q = {!!}

-- The proofs are much easier without inner product proof, which should be
-- transferrable if ⟨x,Ay⟩≡⟨y,Aᵀx⟩-UIP is provable.
M↓≡→M≡ : ⦃ F : Field A ⦄ → (C D : M A ∶ m × n) → (M→M↓ C ≡ M→M↓ D) → C ≡ D
M↓≡→M≡ ⟦ C , Cᵀ , p ⟧ ⟦ .C , .Cᵀ , q ⟧ l@refl rewrite
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
          → (L *ᴹ R) ᵀ ≡ R ᵀ *ᴹ L ᵀ
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
-- *ᴹ-distr-+ᴹ↓ ⟦ X , Xᵀ , Xₚ ⟧ ⟦ Y , Yᵀ , Yₚ ⟧ ⟦ Z , Zᵀ , Zₚ ⟧ rewrite *ˡᵐ-distr-+ˡᵐₗ X Y Z | *ˡᵐ-distr-+ˡᵐᵣ Yᵀ Zᵀ Xᵀ = refl
