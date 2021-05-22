open import net.cruhland.axioms.Cast using (_As_; _as_)
open import net.cruhland.models.Function using (const)
open import net.cruhland.models.Logic using (⊤)

-- To use this module, just `open import` it
module net.cruhland.models.Literals where

-- Export definitions necessary to support custom literals
open import Agda.Builtin.Nat public using (Nat)
open import net.cruhland.models.Logic public using (⊤-intro)

record FromLiteral_~_ (A : Set) (C : Nat → Set) : Set where
  constructor FromLiteral-intro
  field
    fromNat : ∀ n → {{_ : C n}} → A

open FromLiteral_~_ {{...}} public using (fromNat)

{-# BUILTIN FROMNAT fromNat #-}
{-# DISPLAY FromLiteral_~_.fromNat _ n = fromNat n #-}

FromLiteral : Set → Set
FromLiteral A = FromLiteral A ~ const ⊤

literal-from-cast : {A : Set} {{_ : Nat As A}} → FromLiteral A
literal-from-cast {A} = FromLiteral-intro (_as A)
