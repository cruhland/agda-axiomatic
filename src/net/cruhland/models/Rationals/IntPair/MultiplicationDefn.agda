open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Rationals.IntPair.MultiplicationDefn
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.axioms.Rationals.MultiplicationDecl PA Z
  using (Multiplication)
open import net.cruhland.models.Rationals.IntPair.AdditionDefn PA Z using (QA)
open import net.cruhland.models.Rationals.IntPair.BaseDefn PA Z using (QB)
import net.cruhland.models.Rationals.IntPair.MultiplicationImpl PA Z as QM
open import net.cruhland.models.Rationals.IntPair.NegationDefn PA Z using (QN)

QM : Multiplication QB QA QN
QM = record { QM }
