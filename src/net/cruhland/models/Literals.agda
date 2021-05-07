open import Agda.Builtin.Nat using (Nat)
open import net.cruhland.axioms.Cast using (_As_; _as_)
open import net.cruhland.models.Function using (const)
open import net.cruhland.models.Logic using (⊤)

-- To use this module, just `open import` it
module net.cruhland.models.Literals where

-- Export definitions necessary to support custom literals
open import Agda.Builtin.FromNat public using (fromNat; Number)
open import net.cruhland.axioms.Cast public using (id-cast)
open import net.cruhland.models.Logic public using (⊤-intro)

instance
  number-from-cast : {A : Set} {{_ : Nat As A}} → Number A
  number-from-cast {A} = record { Constraint = const ⊤ ; fromNat = _as A }
