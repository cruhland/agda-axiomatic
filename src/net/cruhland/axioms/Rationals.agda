open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Rationals
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.axioms.Rationals.BaseDecl PA Z using (Base)

record Rationals : Set₁ where
  field
    QB : Base

  open Base QB public
