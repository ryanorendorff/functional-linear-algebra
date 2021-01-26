{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open ≡-Reasoning

open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties

open import Data.Product using (_,_)
open import Data.Vec using (Vec; foldr; zipWith; map; []; _∷_; _++_; take; drop; splitAt; replicate)
open import Data.Vec.Properties

module FLA.Data.Vec.Properties where

private
  variable
    ℓ : Level
    A B C : Set ℓ
    m n : ℕ

++-identityₗ : (v : Vec A n) → [] ++  v ≡ v
++-identityₗ _ = refl
