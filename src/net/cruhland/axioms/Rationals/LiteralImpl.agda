open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Rationals.BaseDecl using (Base)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Rationals.LiteralImpl
  (PA : PeanoArithmetic) (Z : Integers PA) (QB : Base PA Z) where

private open module ℤ = Integers Z using (ℤ)
private open module ℚ = Base QB using (ℚ)

instance
  nat-literal : FromNatLiteral ℚ
  nat-literal = nat-literal-via ℤ