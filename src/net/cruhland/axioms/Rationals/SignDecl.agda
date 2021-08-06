open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
import net.cruhland.axioms.Sign as S
open import net.cruhland.models.Literals

module net.cruhland.axioms.Rationals.SignDecl
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.axioms.Rationals.BaseDecl PA Z using (Base)
import net.cruhland.axioms.Rationals.LiteralImpl PA Z as LiteralImpl

private module RationalPredefs (QB : Base) where
  open Base QB public
  open LiteralImpl QB public

record Sign (QB : Base) : Set₁ where
  private open module ℚ = RationalPredefs QB using (ℚ)

  field
    {{positivity}} : S.Positivity 0
    {{negativity}} : S.Negativity 0
