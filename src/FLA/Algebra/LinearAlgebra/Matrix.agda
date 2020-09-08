{-# OPTIONS --without-K --safe #-}

open import Level using (Level)
open import Data.Nat using (ℕ; suc; zero)

open import Data.Empty

open import Data.Vec using (Vec; foldr; zipWith; map)
open import Data.Product hiding (map; _,_)

open import Relation.Binary.PropositionalEquality hiding (Extensionality)
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

module _ ⦃ F : Field A ⦄ where
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
          ⟨ x , M₁ ·ˡᵐ y +ⱽ M₂ ·ˡᵐ y ⟩          ≡⟨ ⟨x,y+z⟩≡⟨x,y⟩+⟨x,z⟩ x
                                                   (M₁ ·ˡᵐ y) (M₂ ·ˡᵐ y) ⟩
          ⟨ x , M₁ ·ˡᵐ y ⟩ + ⟨ x , M₂ ·ˡᵐ y ⟩   ≡⟨ cong (_+ ⟨ x , M₂ ·ˡᵐ y ⟩)
                                                        (M₁-proof x y) ⟩
          ⟨ y , M₁ᵀ ·ˡᵐ x ⟩ + ⟨ x , M₂ ·ˡᵐ y ⟩  ≡⟨ cong (⟨ y , M₁ᵀ ·ˡᵐ x ⟩ +_)
                                                        (M₂-proof x y) ⟩
          ⟨ y , M₁ᵀ ·ˡᵐ x ⟩ + ⟨ y , M₂ᵀ ·ˡᵐ x ⟩ ≡⟨ sym (⟨x,y+z⟩≡⟨x,y⟩+⟨x,z⟩ y
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

infixr 20 _·_
infixl 25 _ᵀ


-- Matrix Free Operators ------------------------------------------------------

module _ ⦃ F : Field A ⦄ where
  open Field F

  I : M A ∶ n × n
  I = ⟦ idₗₘ , idₗₘ , id-transpose  ⟧
    where
      id-transpose : (x y : Vec A n)
                   → ⟨ x , id y ⟩ ≡ ⟨ y , id x ⟩
      id-transpose x y rewrite
          zipWith-comm (_*_) (*-comm) x y
        = refl

diag : ⦃ F : Field A ⦄ → Vec A n → M A ∶ n × n
diag d = ⟦ diagₗₘ d , diagₗₘ d , diag-transpose d ⟧
  where
    diag-transpose : ⦃ F : Field A ⦄ → (d : Vec A n) → (x y : Vec A n)
                   → ⟨ x , diagₗₘ d ·ˡᵐ y ⟩ ≡ ⟨ y , diagₗₘ d ·ˡᵐ x ⟩
    diag-transpose {{F}} d x y =
      begin
        ⟨ x , diagₗₘ d ·ˡᵐ y ⟩ ≡⟨⟩
        sum (x ∘ⱽ (d ∘ⱽ y))    ≡⟨ cong (sum) (∘ⱽ-comm x (d ∘ⱽ y)) ⟩
        sum ((d ∘ⱽ y) ∘ⱽ x)    ≡⟨ cong (λ dy → sum (dy ∘ⱽ x)) (∘ⱽ-comm d y) ⟩
        sum ((y ∘ⱽ d) ∘ⱽ x)    ≡⟨ cong sum (∘ⱽ-assoc y d x) ⟩
        sum (y ∘ⱽ (d ∘ⱽ x))    ≡⟨⟩
        ⟨ y , diagₗₘ d ·ˡᵐ x ⟩ ∎
