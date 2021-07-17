open import net.cruhland.axioms.Eq using (_≄ⁱ_)
open import net.cruhland.axioms.Integers using (Integers)
import net.cruhland.axioms.Operators as Op
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Rationals.ReciprocalDecl
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.axioms.Rationals.BaseDecl PA Z using (Base)

record Reciprocal (QB : Base) : Set where
  open Base QB using (ℚ)

  field
    {{reciprocal}} : Op.SupNegOne ℚ (_≄ⁱ 0)
