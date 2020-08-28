{-# OPTIONS --without-K #-}

open import Axiom.Extensionality.Propositional

module FLA.Axiom.Extensionality.Propositional where

-- Since (dependent) extensionality is not allowed in standard Agda, we
-- postulate it here. In the standard library, the Extensionality term is
-- given in the type, which is then often named `ext` as an input to the
-- function. However this is cumberson, as anything using extensionality now
-- needs to take extensionality as an argument. If this library was
-- converted to cubical Agda we could prove extensionality directly,
-- although we would lose UIP.
postulate
  extensionality : ∀ {α β} → Extensionality α β
