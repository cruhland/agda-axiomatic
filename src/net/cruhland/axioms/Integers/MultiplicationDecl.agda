open import net.cruhland.axioms.Operators using (Star)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Integers.MultiplicationDecl
  (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)

record Multiplication (ZB : Base) : Set where
  open Base ZB using (ℤ)

  field
    {{star}} : Star ℤ
