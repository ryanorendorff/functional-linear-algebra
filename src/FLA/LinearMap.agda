module FLA.LinearMap where

open import Level using (Level)
open import Data.Nat using (ℕ; suc; zero)

open import Data.Empty

open import Data.Vec using (Vec; foldr; zipWith; map)
                     renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
-- open import Data.Product hiding (map)

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Function using (id)

private
  variable
    ℓ : Level
    A : Set ℓ
    m n p q : ℕ


-- TODO: Can this be replaced with something like the List⁺ definition so that
-- the proofs from Vec can be transferred? This definition is convenient because
-- the size is correct (it is not n - 1).
data Vec⁺ (A : Set ℓ) : ℕ → Set ℓ where
  [_] : A → Vec⁺ A 1
  _∷_ : ∀ {n} (x : A) (xs : Vec⁺ A n) → Vec⁺ A (suc n)

infixr 5 _∷_

-- Want to prove that is it not possible to construct an empty vector
emptyVecImpossible : Vec⁺ A 0 → ⊥
emptyVecImpossible = λ ()

Vec⁺→Vec : Vec⁺ A n → Vec A n
Vec⁺→Vec [ v ] = v ∷ⱽ []ⱽ
Vec⁺→Vec (v ∷ vs⁺) = v ∷ⱽ Vec⁺→Vec vs⁺

Vec⁺→n≢0 : Vec⁺ A n → n ≢ 0
Vec⁺→n≢0 {ℓ} {A} {suc n} v = suc≢0
  where
    suc≢0 : {n : ℕ} → suc n ≢ 0
    suc≢0 {zero} ()
    suc≢0 {suc n} = λ ()

-- Closer maybe but still buggered
-- Vec→Vec⁺ : ∀ {ℓ} → {A : Set ℓ} {n : ℕ} → (n ≢ 0) → Vec A n → Vec⁺ A n
-- Vec→Vec⁺ {ℓ} {A} {0} p []ⱽ = ⊥-elim (p refl)
-- Vec→Vec⁺ {ℓ} {A} {1} p (x ∷ⱽ []ⱽ) = [ x ]
-- Vec→Vec⁺ {ℓ} {A} {suc n} p (x ∷ⱽ xs) = x ∷ (Vec→Vec⁺ {!!} xs)

record Field (A : Set ℓ) : Set ℓ where

  infixl 6 _+_
  infixl 7 _*_
  infixl 9 -_
  infixl 10 _⁻¹

  field
    _+_ : A → A → A
    _*_ : A → A → A

    0ᶠ   : A
    1ᶠ   : A
    -_   : A → A -- + inverse
    _⁻¹  : A → A -- * inverse

    +-assoc   : (a b c : A) → a + (b + c) ≡ (a + b) + c
    +-comm    : (a b : A)   → a + b ≡ b + a
    +-0       : (a : A)     → a + 0ᶠ ≡ a
    +-inv     : (a : A)     → - a + a ≡ 0ᶠ
    *-assoc   : (a b c : A) → a * (b * c) ≡ (a * b) * c
    *-comm    : (a b : A)   → a * b ≡ b * a
    *-1       : (a : A)     → a * 1ᶠ ≡ a
    *-inv     : (a : A)     → (a ≢ 0ᶠ) → a ⁻¹ * a ≡ 1ᶠ
    *-distr-+ : (a b c : A) → a * (b + c) ≡ a * b + a * c

private
  variable
    ⦃ F ⦄ : Field A


module FieldProperties ⦃ F : Field A ⦄ where
  open Field {{...}}

  0ᶠ+0ᶠ≡0ᶠ : 0ᶠ + 0ᶠ ≡ 0ᶠ
  0ᶠ+0ᶠ≡0ᶠ = +-0 0ᶠ

open FieldProperties

{-
If we want the reals, we need a few things

Linearly ordered set on F, ∀ x, y, z ∈ F
  Totality : x ≤ y or y ≤ x
  Transitivity : if x ≤ y and y ≤ z then x ≤ z
  Anti-symmetry : if x ≤ y and y ≤ x, then x ≡ y

Linearly ordered field (F, +, *, ≤) if
  x ≤ y then z + x ≤ z + y
  0 ≤ x and 0 ≤ y then 0 ≤ x*y

Complete ordered field (F, +, *, ≤) if
  (F, +, *, ≤) is a linearly ordered field
  Completeness : every non-empty subset of F, bounded above, has a supremum in F

Archimedian property:
  (F, +, *, ≤) is a complete ordered field
  r, s ∈ F. r > 0 ∃ n ∈ ℕ. s < r + ... + r (n times)

  Roughly speaking, it is the property of having no infinitely large or
  infinitely small elements

  Axiom of Archimedies is a formulation of this property for ordered fields:
    ∀ ε ∈ F. ε > 0 → ∃ n ∈ ℕ . 1/n < ε

Cauchy sequences representation of the reals and the Dedekind representation
of the reals are both Archimedian completely ordered fields and hence
isomorphic to the reals. Note there is a proof that all Archimedian complete
ordered fields are isomorphic.

References:
[1]: https://www.cs.swan.ac.uk/~csetzer/articlesFromOthers/chiMing/chiMingChuangExtractionOfProgramsForExactRealNumberComputation.pdf
[2]: https://en.wikipedia.org/wiki/Axiomatic_theory_of_real_numbers
-}


-- Binary operators on vectors ------------------------------------------------

_+ⱽ_ : ⦃ F : Field A ⦄ → Vec A n → Vec A n → Vec A n
_+ⱽ_ []ⱽ []ⱽ = []ⱽ
_+ⱽ_ (x₁ ∷ⱽ xs₁) (x₂ ∷ⱽ xs₂) = x₁ + x₂ ∷ⱽ (xs₁ +ⱽ xs₂)
  where open Field {{...}}

-- Vector Hadamard product
_∘ⱽ_ : ⦃ F : Field A ⦄ → Vec A n → Vec A n → Vec A n
_∘ⱽ_ = zipWith _*_
  where open Field {{...}}

-- Multiply vector by a constant
_*ᶜ_ : ⦃ F : Field A ⦄ → A → Vec A n → Vec A n
c *ᶜ v = map (c *_) v
  where open Field {{...}}

-- Match the fixity of Haskell
infixl  6 _+ⱽ_
infixl  7 _∘ⱽ_
infixl 10 _*ᶜ_

sum : ⦃ F : Field A ⦄ → Vec A n → A
sum = foldr _ _+_ 0ᶠ
  where open Field {{...}}

module sumProperties ⦃ F : Field A ⦄ where
  open Field F

  sum-distr-+ⱽ : (v₁ v₂ : Vec A n) → sum (v₁ +ⱽ v₂) ≡ sum v₁ + sum v₂
  sum-distr-+ⱽ []ⱽ []ⱽ = sym (0ᶠ+0ᶠ≡0ᶠ)
  sum-distr-+ⱽ (v₁ ∷ⱽ vs₁) (v₂ ∷ⱽ vs₂) rewrite
      sum-distr-+ⱽ vs₁ vs₂
    | +-assoc (v₁ + v₂) (foldr (λ v → A) _+_ 0ᶠ vs₁) (foldr (λ v → A) _+_ 0ᶠ vs₂)
    | sym (+-assoc v₁ v₂ (foldr (λ v → A) _+_ 0ᶠ vs₁))
    | +-comm v₂ (foldr (λ v → A) _+_ 0ᶠ vs₁)
    | +-assoc v₁ (foldr (λ v → A) _+_ 0ᶠ vs₁) v₂
    | sym (+-assoc (v₁ + (foldr (λ v → A) _+_ 0ᶠ vs₁)) v₂ (foldr (λ v → A) _+_ 0ᶠ vs₂))
    = refl

open sumProperties

-- Inner product
⟨_,_⟩ : ⦃ F : Field A ⦄ → Vec A n → Vec A n → A
⟨ v₁ , v₂ ⟩ =  sum (v₁ ∘ⱽ v₂)


-------------------------------------------------------------------------------
--                             Proofs on Vectors                             --
-------------------------------------------------------------------------------

zipWith-comm : (f : A → A → A) → (f-comm : (a b : A) → f a b ≡ f b a)
             → (x y : Vec A n) → zipWith f x y ≡ zipWith f y x
zipWith-comm f f-comm []ⱽ []ⱽ = refl
zipWith-comm f f-comm (x ∷ⱽ xs) (y ∷ⱽ ys) rewrite
    zipWith-comm f f-comm xs ys
  | f-comm x y = refl

+ⱽ-assoc : ⦃ F : Field A ⦄ → (v₁ v₂ v₃ : Vec A n)
         → v₁ +ⱽ v₂ +ⱽ v₃ ≡ v₁ +ⱽ (v₂ +ⱽ v₃)
+ⱽ-assoc []ⱽ []ⱽ []ⱽ = refl
+ⱽ-assoc ⦃ F ⦄ (v₁ ∷ⱽ vs₁) (v₂ ∷ⱽ vs₂) (v₃ ∷ⱽ vs₃) rewrite
    +ⱽ-assoc vs₁ vs₂ vs₃
  | Field.+-assoc F v₁ v₂ v₃
    = refl

+ⱽ-comm : ⦃ F : Field A ⦄ → (v₁ v₂ : Vec A n) → v₁ +ⱽ v₂ ≡ v₂ +ⱽ v₁
+ⱽ-comm []ⱽ []ⱽ = refl
+ⱽ-comm (x₁ ∷ⱽ vs₁) (x₂ ∷ⱽ vs₂) = begin
  x₁ + x₂ ∷ⱽ vs₁ +ⱽ vs₂
  ≡⟨ cong ((x₁ + x₂) ∷ⱽ_) (+ⱽ-comm vs₁ vs₂) ⟩
  x₁ + x₂ ∷ⱽ vs₂ +ⱽ vs₁
  ≡⟨ cong (_∷ⱽ vs₂ +ⱽ vs₁) (+-comm x₁ x₂) ⟩
  x₂ + x₁ ∷ⱽ vs₂ +ⱽ vs₁
  ∎
  where open Field {{...}}

∘ⱽ-comm : ⦃ F : Field A ⦄ → (v₁ v₂ : Vec A n) → v₁ ∘ⱽ v₂ ≡ v₂ ∘ⱽ v₁
∘ⱽ-comm []ⱽ []ⱽ = refl
∘ⱽ-comm ⦃ F ⦄ (v₁ ∷ⱽ vs₁) (v₂ ∷ⱽ vs₂) rewrite
    ∘ⱽ-comm vs₁ vs₂
  | Field.*-comm F v₁ v₂
  = refl

∘ⱽ-distr-+ⱽ : ⦃ F : Field A ⦄ → (a u v : Vec A n)
            → a ∘ⱽ (u +ⱽ v) ≡ a ∘ⱽ u +ⱽ a ∘ⱽ v
∘ⱽ-distr-+ⱽ []ⱽ []ⱽ []ⱽ = refl
∘ⱽ-distr-+ⱽ ⦃ F ⦄ (a ∷ⱽ as) (u ∷ⱽ us) (v ∷ⱽ vs) rewrite
    ∘ⱽ-distr-+ⱽ as us vs
  | Field.*-distr-+ F a u v
  = refl

-- Homogeneity of degree 1 for linear maps
∘ⱽ*ᶜ≡*ᶜ∘ⱽ : ⦃ F : Field A ⦄ → (c : A) (u v : Vec A n)
          → u ∘ⱽ c *ᶜ v ≡ c *ᶜ (u ∘ⱽ v)
∘ⱽ*ᶜ≡*ᶜ∘ⱽ c []ⱽ []ⱽ = refl
∘ⱽ*ᶜ≡*ᶜ∘ⱽ ⦃ F ⦄ c (u ∷ⱽ us) (v ∷ⱽ vs) rewrite
    ∘ⱽ*ᶜ≡*ᶜ∘ⱽ c us vs
  | Field.*-assoc F u c v
  | Field.*-comm F u c
  | sym (Field.*-assoc F c u v)
  = refl

*ᶜ-distr-+ⱽ : ⦃ F : Field A ⦄
            → (c : A) (u v : Vec A n)
            → c *ᶜ (u +ⱽ v) ≡ c *ᶜ u +ⱽ c *ᶜ v
*ᶜ-distr-+ⱽ c []ⱽ []ⱽ = refl
*ᶜ-distr-+ⱽ ⦃ F ⦄ c (u ∷ⱽ us) (v ∷ⱽ vs) rewrite
    *ᶜ-distr-+ⱽ c us vs
  | Field.*-distr-+ F c u v
  = refl

⟨⟩-comm : ⦃ F : Field A ⦄ → (v₁ v₂ : Vec A n)
        → ⟨ v₁ , v₂ ⟩ ≡ ⟨ v₂ , v₁ ⟩
⟨⟩-comm []ⱽ []ⱽ = refl
⟨⟩-comm ⦃ F ⦄ (x₁ ∷ⱽ v₁) (x₂ ∷ⱽ v₂) rewrite
    ⟨⟩-comm v₁ v₂
  | Field.*-comm F x₁ x₂
  = refl


-- Should we show bilinearity?
--   ∀ λ ∈ F, B(λv, w) ≡ B(v, λw) ≡ λB(v, w)
--   B(v₁ + v₂, w) ≡ B(v₁, w) + B(v₂, w) ∧ B(v, w₁ + w₂) ≡ B(v, w₁) + B(v, w₂)
-- Additivity in both arguments
module ⟨⟩-Properties ⦃ F : Field A ⦄ where
  open Field F

  ⟨x+y,z⟩≡⟨x,z⟩+⟨y,z⟩ : (x y z : Vec A n)
                      → ⟨ x +ⱽ y , z ⟩ ≡ (⟨ x , z ⟩) + (⟨ y , z ⟩)
  ⟨x+y,z⟩≡⟨x,z⟩+⟨y,z⟩ x y z = begin
    ⟨ x +ⱽ y , z ⟩
    ≡⟨⟩
    sum ((x +ⱽ y) ∘ⱽ z )
    ≡⟨ cong sum (∘ⱽ-comm (x +ⱽ y) z) ⟩
    sum (z ∘ⱽ (x +ⱽ y))
    ≡⟨ cong sum (∘ⱽ-distr-+ⱽ z x y) ⟩
    sum (z ∘ⱽ x +ⱽ z ∘ⱽ y)
    ≡⟨ sum-distr-+ⱽ (z ∘ⱽ x) (z ∘ⱽ y) ⟩
    sum (z ∘ⱽ x) + sum (z ∘ⱽ y)
    ≡⟨⟩
    ⟨ z , x ⟩ + ⟨ z , y ⟩
    ≡⟨ cong (_+ ⟨ z , y ⟩) (⟨⟩-comm z x) ⟩
    ⟨ x , z ⟩ + ⟨ z , y ⟩
    ≡⟨ cong (⟨ x , z ⟩ +_ ) (⟨⟩-comm z y) ⟩
    ⟨ x , z ⟩ + ⟨ y , z ⟩
    ∎

  ⟨x,y+z⟩≡⟨x,y⟩+⟨x,z⟩ : (x y z : Vec A n)
                      → ⟨ x , y +ⱽ z ⟩ ≡ (⟨ x , y ⟩) + (⟨ x , z ⟩)
  ⟨x,y+z⟩≡⟨x,y⟩+⟨x,z⟩ x y z = begin
    ⟨ x , y +ⱽ z ⟩
    ≡⟨ ⟨⟩-comm x (y +ⱽ z) ⟩
    ⟨ y +ⱽ z , x ⟩
    ≡⟨ ⟨x+y,z⟩≡⟨x,z⟩+⟨y,z⟩ y z x ⟩
    ⟨ y , x ⟩ + ⟨ z , x ⟩
    ≡⟨ cong (_+ ⟨ z , x ⟩) (⟨⟩-comm y x) ⟩
    ⟨ x , y ⟩ + ⟨ z , x ⟩
    ≡⟨ cong (⟨ x , y ⟩ +_ ) (⟨⟩-comm z x) ⟩
    ⟨ x , y ⟩ + ⟨ x , z ⟩
    ∎

open ⟨⟩-Properties

-------------------------------------------------------------------------------
--                           LinearMap constructor                           --
-------------------------------------------------------------------------------

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

  ·-distr-+ⱽ : (M : M A ∶ m × n) → (u v : Vec A n)
            → M · (u +ⱽ v) ≡ M · u +ⱽ M · v
  ·-distr-+ⱽ ⟦ M , _ , _ ⟧ u v = LinearMap.f[u+v]≡f[u]+f[v] M u v

  ·-comm-*ᶜ : (M : M A ∶ m × n) → (c : A) (v : Vec A n)
            → M · (c *ᶜ v) ≡ c *ᶜ (M · v)
  ·-comm-*ᶜ ⟦ M , _ , _ ⟧ c v = LinearMap.f[c*v]≡c*f[v] M c v

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
--                                Proofs on M                                --
-------------------------------------------------------------------------------

-- The thought here is that maybe I can copy the proof once I prove the
-- first two components are the same.

data M↓_∶_×_ (A : Set ℓ) ⦃ F : Field A ⦄ (m n : ℕ) : Set ℓ where
  ⟦_,_⟧ : (M : LinearMap A n m ) → (Mᵀ : LinearMap A m n ) → M↓ A ∶ m × n

exF : ⦃ F : Field A ⦄ → M↓ A ∶ m × n → LinearMap A n m
exF ⟦ M , Mᵀ ⟧ = M

exA : ⦃ F : Field A ⦄ → M↓ A ∶ m × n → LinearMap A m n
exA ⟦ M , Mᵀ ⟧ = Mᵀ

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

-- forwardAjointProofs : ⦃ F : Field A ⦄
--                     → (C D : M↓ A ∶ m × n)
--                     → C ≡ D
--                     → ( exF C ≡ exF D  , exA C ≡ exA D )
-- forwardAjointProofs C D C≡D = ?

ᵀᵀ : {A : Set} ⦃ F : Field A ⦄ → (B : M A ∶ m × n) → M→M↓ (B ᵀ ᵀ) ≡ M→M↓ B
ᵀᵀ ⟦ M , Mᵀ , p ⟧ = refl

ᵀ-distr-* : {A : Set} ⦃ F : Field A ⦄ → (L : M A ∶ m × n) (R : M A ∶ n × p)
          → M→M↓ ((L *ᴹ R) ᵀ) ≡ M→M↓ (R ᵀ *ᴹ L ᵀ)
ᵀ-distr-* ⟦ L , Lᵀ , p ⟧ ⟦ R , Rᵀ₁ , q ⟧ = refl

ᵀ-distr-+ : {A : Set} ⦃ F : Field A ⦄
          → (L : M A ∶ m × n) (R : M A ∶ m × n)
          → M→M↓ ((L +ᴹ R) ᵀ) ≡ M→M↓ (L ᵀ +ᴹ R ᵀ)
ᵀ-distr-+ ⟦ L , Lᵀ , p ⟧ ⟦ R , Rᵀ , q ⟧ = refl


-- z : ⦃ F : Field A ⦄ → (C D : M A ∶ m × n) → (M→M↓ C ≡ M→M↓ D) → C ≡ D
-- z ⟦ C , Cᵀ , p ⟧ ⟦ D , Dᵀ , q ⟧ C↓≡D↓ = {!!}
