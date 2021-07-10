open import net.cruhland.axioms.Integers using (Integers)
import net.cruhland.axioms.Operators as Op
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Rationals.MultiplicationDecl
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.axioms.Rationals.BaseDecl PA Z using (Base)

record Multiplication (QB : Base) : Set where
  open Base QB using (ℚ)

  field
    {{star}} : Op.Star ℚ
