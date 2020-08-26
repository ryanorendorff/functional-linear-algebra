{-# OPTIONS --without-K --safe #-}

module FLA.Data.VectorList where

open import Data.List using (List; sum) renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)
open import Data.Nat using (ℕ; _+_; zero; suc)
open import Data.Vec using (Vec; _++_) renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Product as Prod using (∃; ∃₂; _×_; _,_)

-- At the moment, `VectorList` is named `RList` in the Haskell code.
data VectorList (A : Set) : List ℕ → Set where
  []ⱽᴸ  : VectorList A []ᴸ
  _∷ⱽᴸ_ : {n : ℕ} {ns : List ℕ} → Vec A n → VectorList A ns
                                → VectorList A (n ∷ᴸ ns)
infixr 5 _∷ⱽᴸ_

concat : {A : Set} {ns : List ℕ} → VectorList A ns → Vec A (sum ns)
concat []ⱽᴸ = []ⱽ
concat (v ∷ⱽᴸ vs) = v ++ concat vs

-- We will want to use split to split a VectorList
split : {A : Set} → {m n : ℕ} → Vec A (m + n) → Vec A m × Vec A n
split {A} {zero} {n} v = []ⱽ , v
split {A} {suc m} {n} (v ∷ⱽ vs) = let v₁ , v₂ = split vs in v ∷ⱽ v₁ , v₂

-- Hmm, this will be hard to translate to Haskell, since we match on ns
splitToVectorList : {A : Set} → (ns : List ℕ) → Vec A (sum ns) → VectorList A ns
splitToVectorList []ᴸ v = []ⱽᴸ
splitToVectorList (_ ∷ᴸ ns) v = let v₁ , v₂ = split v in
                                v₁ ∷ⱽᴸ (splitToVectorList ns v₂)

