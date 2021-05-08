import net.cruhland.axioms.Operators as Op
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Integers.NegationDecl (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)

record Negation (ZB : Base) : Set where
  open Base ZB using (ℤ)

  field
    {{neg-dash}} : Op.Dashᴸ ℤ
