open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Rationals.IntPair.ReciprocalDefn
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.axioms.Rationals.ReciprocalDecl PA Z using (Reciprocal)
open import net.cruhland.models.Rationals.IntPair.AdditionDefn PA Z using (QA)
open import net.cruhland.models.Rationals.IntPair.BaseDefn PA Z using (QB)
open import net.cruhland.models.Rationals.IntPair.MultiplicationDefn PA Z
  using (QM)
open import net.cruhland.models.Rationals.IntPair.NegationDefn PA Z using (QN)
import net.cruhland.models.Rationals.IntPair.ReciprocalImpl PA Z as QR

QR : Reciprocal QB QA QN QM
QR = record { QR }
