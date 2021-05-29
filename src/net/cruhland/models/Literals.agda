open import net.cruhland.axioms.Cast using (_As_; _as_)
open import net.cruhland.models.Function using (const)
open import net.cruhland.models.Logic using (⊤)

-- To use this module, just `open import` it
module net.cruhland.models.Literals where

-- Export definitions necessary to support custom literals
open import Agda.Builtin.Nat public using (Nat)
open import net.cruhland.models.Logic public using (⊤-intro)

record FromNatLiteral_~_ (A : Set) (C : Nat → Set) : Set where
  constructor FromNatLiteral-intro
  field
    fromNatLiteral : ∀ n → {{_ : C n}} → A

open FromNatLiteral_~_ {{...}} public using (fromNatLiteral)

{-# BUILTIN FROMNAT fromNatLiteral #-}
{-# DISPLAY FromNatLiteral_~_.fromNatLiteral _ n = fromNatLiteral n #-}

FromNatLiteral : Set → Set
FromNatLiteral A = FromNatLiteral A ~ const ⊤

nat-literal-from-cast : {A : Set} {{_ : Nat As A}} → FromNatLiteral A
nat-literal-from-cast {A} = FromNatLiteral-intro (_as A)

record FromNegLiteral_~_ (A : Set) (C : Nat → Set) : Set where
  constructor FromNegLiteral-intro
  field
    fromNegLiteral : ∀ n → {{_ : C n}} → A

open FromNegLiteral_~_ {{...}} public using (fromNegLiteral)

{-# BUILTIN FROMNEG fromNegLiteral #-}
{-# DISPLAY FromNegLiteral_~_.fromNegLiteral _ n = fromNegLiteral n #-}

FromNegLiteral : Set → Set
FromNegLiteral A = FromNegLiteral A ~ const ⊤
