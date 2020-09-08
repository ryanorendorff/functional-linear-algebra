{-# OPTIONS --with-K --safe #-}

open import Level using (Level)

open import Relation.Binary.HeterogeneousEquality using (_≅_; icong; ≅-to-≡)
  renaming (refl to hrefl; cong to hcong)

open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties

open import Data.Product using (_,_)
open import Data.Vec using (Vec; foldr; zipWith; map; []; _∷_; _++_; take; drop; splitAt)

module FLA.Data.Vec.Properties.WithK where

private
  variable
    ℓ : Level
    A B C : Set ℓ
    m n : ℕ

++-identityᵣ : (v : Vec A n) → v ++ [] ≅ v
++-identityᵣ [] = hrefl
++-identityᵣ {ℓ} {A} {suc n} (v ∷ vs) = icong (Vec A) (+-identityʳ n)
                                              (v ∷_) (++-identityᵣ vs)
