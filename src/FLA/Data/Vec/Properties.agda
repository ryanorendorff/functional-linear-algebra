{-# OPTIONS --without-K --safe #-}


-- open import Relation.Binary.HeterogeneousEquality using (_≅_; icong; ≅-to-≡)
--   renaming (refl to hrefl; cong to hcong)
-- ++-identityᵣ : (v : Vec A n) → v ++ [] ≅ v
-- ++-identityᵣ [] = hrefl
-- ++-identityᵣ {ℓ} {A} {suc n} (v ∷ vs) = icong (Vec A) (+-identityʳ n)
--                                               (v ∷_) (++-identityᵣ vs)

open import Level using (Level)

open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open ≡-Reasoning

open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties

open import Data.Product using (_,_)
open import Data.Vec using (Vec; foldr; zipWith; map; []; _∷_; _++_; take; drop; splitAt)

module FLA.Data.Vec.Properties where

private
  variable
    ℓ : Level
    A B C : Set ℓ
    m n : ℕ

++-identityₗ : (v : Vec A n) → [] ++  v ≡ v
++-identityₗ _ = refl


-------------------------------------------------------------------------------
--                               zipWith proofs                              --
-------------------------------------------------------------------------------

zipWith-comm : (f : A → A → A) → (f-comm : (a b : A) → f a b ≡ f b a)
             → (x y : Vec A n) → zipWith f x y ≡ zipWith f y x
zipWith-comm f f-comm [] [] = refl
zipWith-comm f f-comm (x ∷ xs) (y ∷ ys) rewrite
    zipWith-comm f f-comm xs ys
  | f-comm x y = refl

-------------------------------------------------------------------------------
--                              take/drop proofs                             --
-------------------------------------------------------------------------------

-- TODO: replace with Agda stdlib 1.4 version once released.
unfold-take : ∀ n {m} x (xs : Vec A (n + m))
            → take (suc n) (x ∷ xs) ≡ x ∷ take n xs
unfold-take n x xs with splitAt n xs
unfold-take n x .(xs ++ ys) | xs , ys , refl = refl

-- TODO: replace with Agda stdlib 1.4 version once released.
unfold-drop : ∀ n {m} x (xs : Vec A (n + m))
            → drop (suc n) (x ∷ xs) ≡ drop n xs
unfold-drop n x xs with splitAt n xs
unfold-drop n x .(xs ++ ys) | xs , ys , refl = refl

take-distr-zipWith : (f : A → B → C)
                   → (u : Vec A (m + n))
                   → (v : Vec B (m + n))
                   → take m (zipWith f u v) ≡ zipWith f (take m u) (take m v)
take-distr-zipWith {m = zero} f u v = refl
take-distr-zipWith {m = suc m} f (u ∷ us) (v ∷ vs) =
  begin
      take (suc m) (zipWith f (u ∷ us) (v ∷ vs))
    ≡⟨⟩
      take (suc m) (f u v ∷ (zipWith f us vs))
    ≡⟨ unfold-take m (f u v) (zipWith f us vs) ⟩
      f u v ∷ take m (zipWith f us vs)
    ≡⟨ cong (f u v ∷_) (take-distr-zipWith f us vs) ⟩
      f u v ∷ (zipWith f (take m us) (take m vs))
    ≡⟨⟩
      zipWith f (u ∷ (take m us)) (v ∷ (take m vs))
    ≡⟨ cong₂ (zipWith f) (sym (unfold-take m u us)) (sym (unfold-take m v vs)) ⟩
      zipWith f (take (suc m) (u ∷ us)) (take (suc m) (v ∷ vs))
  ∎

drop-distr-zipWith : (f : A → B → C)
                   → (u : Vec A (m + n))
                   → (v : Vec B (m + n))
                   → drop m (zipWith f u v) ≡ zipWith f (drop m u) (drop m v)
drop-distr-zipWith {m = zero} f u v = refl
drop-distr-zipWith {m = suc m} f (u ∷ us) (v ∷ vs) =
  begin
      drop (suc m) (zipWith f (u ∷ us) (v ∷ vs))
    ≡⟨⟩
      drop (suc m) (f u v ∷ (zipWith f us vs))
    ≡⟨ unfold-drop m (f u v) (zipWith f us vs) ⟩
      drop m (zipWith f us vs)
    ≡⟨ drop-distr-zipWith f us vs ⟩
      zipWith f (drop m us) (drop m vs)
    ≡⟨ cong₂ (zipWith f) (sym (unfold-drop m u us)) (sym (unfold-drop m v vs)) ⟩
      zipWith f (drop (suc m) (u ∷ us)) (drop (suc m) (v ∷ vs))
  ∎

take-distr-map : (f : A → B) → (m : ℕ) → (v : Vec A (m + n))
               → take m (map f v) ≡ map f (take m v)
take-distr-map f zero v = refl
take-distr-map f (suc m) (v ∷ vs) =
  begin
    take (suc m) (map f (v ∷ vs)) ≡⟨⟩
    take (suc m) (f v ∷ map f vs) ≡⟨ unfold-take m (f v) (map f vs) ⟩
    f v ∷ (take m (map f vs))     ≡⟨ cong (f v ∷_) (take-distr-map f m vs) ⟩
    f v ∷ (map f (take m vs))     ≡⟨⟩
    map f (v ∷ take m vs)         ≡⟨ cong (map f) (sym (unfold-take m v vs)) ⟩
    map f (take (suc m) (v ∷ vs)) ∎

drop-distr-map : (f : A → B) → (m : ℕ) → (v : Vec A (m + n))
               → drop m (map f v) ≡ map f (drop m v)
drop-distr-map f zero v = refl
drop-distr-map f (suc m) (v ∷ vs) =
  begin
    drop (suc m) (map f (v ∷ vs)) ≡⟨⟩
    drop (suc m) (f v ∷ map f vs) ≡⟨ unfold-drop m (f v) (map f vs) ⟩
    drop m (map f vs)             ≡⟨ drop-distr-map f m vs ⟩
    map f (drop m vs)             ≡⟨ cong (map f) (sym (unfold-drop m v vs)) ⟩
    map f (drop (suc m) (v ∷ vs)) ∎
